import OAI.Geometry.Perimeter.Regularity.EllipticLocalExtension
import OAI.Geometry.Perimeter.Regularity.GeometricHolder
import OAI.Geometry.Perimeter.Regularity.EllipticSecantBounds
import OAI.Geometry.Perimeter.Regularity.LinearDifference

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 abbrev GeoBase {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : ℝ) (f : Euc n → V) (U : Set (Euc n)) : Prop :=
  ContinuousOn f U ∧ ∀ p∈U, GeometricHolderAt θ f p

 def GeoC {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : ℝ) : ℕ → (Euc n → V) → Set (Euc n) → Prop
  | 0,f,U => GeoBase θ f U
  | k+1,f,U => ContDiffOn ℝ 1 f U ∧ GeoBase θ f U ∧
      ∀ e, GeoC θ k (fun x ↦ fderiv ℝ f x e) U

 theorem GeoC.contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k : ℕ} {f : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (h : GeoC θ k f U) : ContDiffOn ℝ k f U := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr h.1
  | succ k ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨h.1.differentiableOn one_ne_zero,by simp,contDiffOn_clm_apply.mpr ?_⟩
    intro e
    exact ih (h.2.2 e)

 theorem GeoC.base {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k : ℕ} {f : Euc n → V} {U : Set (Euc n)}
    (h : GeoC θ k f U) : GeoC θ 0 f U := by cases k with | zero => exact h | succ k => exact h.2.1

 theorem GeoC.mono_order {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k : ℕ} {f : Euc n → V} {U : Set (Euc n)}
    (h : GeoC θ (k+1) f U) : GeoC θ k f U := by
  induction k generalizing f with
  | zero => exact h.2.1
  | succ k ih => exact ⟨h.1,h.2.1,fun e ↦ ih (h.2.2 e)⟩

 theorem GeoC.mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k : ℕ} {f : Euc n → V} {U W : Set (Euc n)}
    (h : GeoC θ k f U) (hWU : W⊆U) : GeoC θ k f W := by
  induction k generalizing f with
  | zero => exact ⟨h.1.mono hWU,fun p hp ↦ h.2 p (hWU hp)⟩
  | succ k ih => exact ⟨h.1.mono hWU,⟨h.2.1.1.mono hWU,fun p hp ↦ h.2.1.2 p (hWU hp)⟩,
      fun e ↦ ih (h.2.2 e)⟩

 theorem GeoC.congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} {f g : Euc n → V} {U : Set (Euc n)}
    (hU : IsOpen U) (h : GeoC θ k f U) (he : EqOn f g U) : GeoC θ k g U := by
  induction k generalizing f g with
  | zero =>
    refine ⟨h.1.congr he.symm,fun p hp ↦ (h.2 p hp).congr hθ ?_⟩
    exact Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx ↦ he hx)
  | succ k ih =>
    refine ⟨h.1.congr he.symm,?_,fun e ↦ ih (h.2.2 e) ?_⟩
    · exact ⟨h.2.1.1.congr he.symm,fun p hp ↦ (h.2.1.2 p hp).congr hθ
        (Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx ↦ he hx))⟩
    · intro x hx
      exact congrArg (fun L : Euc n →L[ℝ] V ↦ L e)
        ((Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy ↦ he hy))))

 theorem GeoC.local {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} {k : ℕ} {f : Euc n → V} {U : Set (Euc n)}
    (h : ∀ p∈U, ∃ W : Set (Euc n), IsOpen W ∧ p∈W ∧ GeoC θ k f W) :
    GeoC θ k f U := by
  induction k generalizing f with
  | zero =>
    constructor
    · intro p hp
      obtain ⟨W,hW,hpW,hh⟩ := h p hp
      exact (hh.1.continuousAt (hW.mem_nhds hpW)).continuousWithinAt
    · intro p hp
      obtain ⟨W,hW,hpW,hh⟩ := h p hp
      exact hh.2 p hpW
  | succ k ih =>
    refine ⟨?_,?_,fun e ↦ ih (fun p hp ↦ ?_)⟩
    · intro p hp
      obtain ⟨W,hW,hpW,hh⟩ := h p hp
      exact (hh.1.contDiffAt (hW.mem_nhds hpW)).contDiffWithinAt
    · constructor
      · intro p hp
        obtain ⟨W,hW,hpW,hh⟩ := h p hp
        exact (hh.1.continuousOn.continuousAt (hW.mem_nhds hpW)).continuousWithinAt
      · intro p hp
        obtain ⟨W,hW,hpW,hh⟩ := h p hp
        exact hh.2.1.2 p hpW
    · obtain ⟨W,hW,hpW,hh⟩ := h p hp
      exact ⟨W,hW,hpW,hh.2.2 e⟩

 theorem geometricHolderAt_of_C1_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) {f : Euc n → V}
    {U : Set (Euc n)} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) {p : Euc n} (hp : p∈U) :
    GeometricHolderAt θ f p := by
  obtain ⟨r,hr,hrU,g,hg,hgc,he⟩ := local_compact_extension hU hp hf
  obtain ⟨s,L,hs,hL,hLip⟩ := contDiff_local_lipschitz hg p
  have hh : GeometricHolderAt θ g p := geometricHolderAt_of_local_lipschitz hθ hθ' hs hL
    (fun x hx y hy ↦ by simpa only [dist_eq_norm] using hLip x hx y hy)
  exact hh.congr hθ (Filter.eventually_of_mem (Metric.ball_mem_nhds p (by positivity : 0<2*r))
    (fun x hx ↦ he x hx))

 theorem geoC_zero_of_C1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/2) {f : Euc n → V}
    {U : Set (Euc n)} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : GeoC θ 0 f U :=
  ⟨hf.continuousOn,fun _ hp ↦ geometricHolderAt_of_C1_on hθ hθ' hU hf hp⟩

end RPISingularHarnack

end

end OAI
