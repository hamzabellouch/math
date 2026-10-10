import Mathlib
import OAI.Analysis.Conductivity.Sobolev.WallPrimitive

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def fiberPrimitive (a : ℝ) (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  wallPrimitive f p-wallPrimitive f (p.1,a)

lemma fiberPrimitive_smooth (a : ℝ) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fiberPrimitive a f) :=
  (wallPrimitive_smooth hf).sub ((wallPrimitive_smooth hf).comp (contDiff_fst.prodMk contDiff_const))

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma fiberPrimitive_eq_integral (a : ℝ) {f : E × ℝ → ℝ} (hf : Continuous f) (p : E × ℝ) :
    fiberPrimitive a f p=∫ t in a..p.2, f (p.1,t) := by
  have hc : Continuous (fun t : ℝ => f (p.1,t)) := hf.comp (continuous_const.prodMk continuous_id)
  change wallPrimitive f (p.1,p.2)-wallPrimitive f (p.1,a)=_
  simp only [wallPrimitive_eq_intervalIntegral]
  exact intervalIntegral.integral_interval_sub_left (μ := volume) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)

lemma fiberPrimitive_derivative (a : ℝ) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallDerivative (fiberPrimitive a f) p=f p := by
  have h := ((fiberPrimitive_smooth a hf).differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hd : HasDerivAt (fun t : ℝ => fiberPrimitive a f (p.1,t)) (f p) p.2 := by
    exact (wallPrimitive_hasDerivAt hf.continuous p.1 p.2).sub_const (wallPrimitive f (p.1,a))
  exact h.unique hd

omit [NormedSpace ℝ E] [ProperSpace E]

lemma fiberPrimitive_of_zero_fiber (a : ℝ) {f : E × ℝ → ℝ} (hf : Continuous f)
    (x : E) (hx : ∀ t, f (x,t)=0) (z : ℝ) : fiberPrimitive a f (x,z)=0 := by
  rw [fiberPrimitive_eq_integral a hf]
  simp only [hx,intervalIntegral.integral_zero]

lemma fiberPrimitive_below {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b) (p : E × ℝ) (hp : p.2≤a) :
    fiberPrimitive a f p=0 := by
  rw [fiberPrimitive_eq_integral a hf]
  calc
    _ = ∫ t in a..p.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hp] at ht
      by_contra hn
      exact (not_lt_of_ge ht.2) (hv (p.1,t) hn).1
    _ = 0 := by simp

lemma fiberPrimitive_above {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hv : ∀ p, f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x, (∫ t in a..b, f (x,t))=0) (p : E × ℝ) (hp : b≤p.2) :
    fiberPrimitive a f p=0 := by
  have hc : Continuous (fun t : ℝ => f (p.1,t)) := hf.comp (continuous_const.prodMk continuous_id)
  rw [fiberPrimitive_eq_integral a hf,←intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a b) (hc.intervalIntegrable b p.2),hz,zero_add]
  calc
    _ = ∫ t in b..p.2, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hp] at ht
      by_contra hn
      exact (not_lt_of_ge ht.1) (hv (p.1,t) hn).2
    _ = 0 := by simp

theorem fiberPrimitive_compact {a b : ℝ} {f : E × ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (hv : ∀ p, f p≠0 → p.2∈Ioo a b)
    (hz : ∀ x, (∫ t in a..b, f (x,t))=0) :
    HasCompactSupport (fiberPrimitive a f) ∧
      tsupport (fiberPrimitive a f) ⊆ (Prod.fst '' tsupport f) ×ˢ Icc a b := by
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ Icc a b) :=
    (hs.image continuous_fst).prod isCompact_Icc
  have hsub : Function.support (fiberPrimitive a f) ⊆ (Prod.fst '' tsupport f) ×ˢ Icc a b := by
    intro p hp
    refine ⟨?_,?_,?_⟩
    · by_contra hx
      have hz' : ∀ t, f (p.1,t)=0 := by
        intro t
        by_contra hn
        exact hx ⟨(p.1,t),subset_tsupport f hn,rfl⟩
      exact hp (fiberPrimitive_of_zero_fiber a hf p.1 hz' p.2)
    · by_contra h
      exact hp (fiberPrimitive_below hf hv p (le_of_lt (lt_of_not_ge h)))
    · by_contra h
      exact hp (fiberPrimitive_above hf hv hz p (le_of_lt (lt_of_not_ge h)))
  refine ⟨HasCompactSupport.of_support_subset_isCompact hK hsub,?_⟩
  exact closure_minimal hsub hK.isClosed

end

open Set MeasureTheory Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compactMomentGram (χ : ℝ → ℝ) (w : ℝ → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ s, χ s*w s i*w s j

omit [Fintype ι] [DecidableEq ι] in
lemma compactMoment_integrable {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (i j : ι) : Integrable (fun s => χ s*w s i*w s j) :=
  ((hc.mul (hw i)).mul (hw j)).integrable_of_hasCompactSupport ((hs.mul_right).mul_right)

omit [DecidableEq ι] in
lemma compactMoment_dot_integrable {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (a : ι → ℝ) : Integrable (fun s => χ s*(a ⬝ᵥ w s)^2) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hc.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul (hw i))).pow 2)
  · exact hs.mul_right

omit [DecidableEq ι] in
lemma compactMoment_quadratic {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (a : ι → ℝ) : a ⬝ᵥ ((compactMomentGram χ w)*ᵥa)=∫ s, χ s*(a ⬝ᵥ w s)^2 := by
  have hi (i j : ι) : Integrable (fun s => a i*(χ s*w s i*w s j)*a j) :=
    ((compactMoment_integrable hc hs hw i j).const_mul _).mul_const _
  calc
    _ = ∑ i, ∑ j, ∫ s, a i*(χ s*w s i*w s j)*a j := by
      simp only [compactMomentGram,mulVec,dotProduct,Finset.mul_sum,
        integral_mul_const,integral_const_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∫ s, ∑ i, ∑ j, a i*(χ s*w s i*w s j)*a j := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [dotProduct,pow_two,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

omit [DecidableEq ι] in
theorem compactMomentGram_posDef {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : Continuous χ) (hs : HasCompactSupport χ) (hw : ∀ i, Continuous (fun s => w s i))
    (hn : ∀ s, 0≤χ s) {l r : ℝ} (hp : ∀ s∈Ioo l r, 0<χ s)
    (hind : ∀ a : ι → ℝ, (∀ s∈Ioo l r, a ⬝ᵥ w s=0) → a=0) :
    (compactMomentGram χ w).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · ext i j
    simp only [conjTranspose_apply,star_trivial,compactMomentGram]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun s => by ring)
  · intro a ha
    simp only [star_trivial]
    rw [compactMoment_quadratic hc hs hw]
    have hnon : ∀ s, 0≤χ s*(a ⬝ᵥ w s)^2 := fun s => mul_nonneg (hn s) (sq_nonneg _)
    apply (integral_nonneg hnon).lt_of_ne'
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg hnon
      (compactMoment_dot_integrable hc hs hw a)).mp hz
    have he := MeasureTheory.Measure.eq_of_ae_eq hae
      (hc.mul ((continuous_finsetSum _ (fun i _ => continuous_const.mul (hw i))).pow 2))
      continuous_zero
    apply ha
    apply hind
    intro s hs
    have h := congrFun he s
    have hsq : (a ⬝ᵥ w s)^2=0 := (mul_eq_zero.mp h).resolve_left (hp s hs).ne'
    nlinarith [sq_nonneg (a ⬝ᵥ w s)]

theorem compactMoment_surjective {χ : ℝ → ℝ} {w : ℝ → ι → ℝ}
    (hc : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hw : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s => w s i))
    (hG : (compactMomentGram χ w).PosDef) (b : ι → ℝ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ tsupport χ ∧ (∀ i, (∫ s, f s*w s i)=b i) := by
  obtain ⟨a,ha⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hG.isUnit b
  refine ⟨fun s => χ s*(a ⬝ᵥ w s),hc.mul ?_,hs.mul_right,tsupport_mul_subset_left,?_⟩
  · exact ContDiff.sum (fun i _ => contDiff_const.mul (hw i))
  · intro i
    rw [←congrFun ha i]
    change (∫ s, χ s*(a ⬝ᵥ w s)*w s i)=∑ j, compactMomentGram χ w i j*a j
    calc
      _ = ∫ s, ∑ j, (χ s*w s i*w s j)*a j := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          simp only [dotProduct,Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl; intro j _; ring)
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ =>
          (compactMoment_integrable hc.continuous hs (fun j => (hw j).continuous) i j).mul_const _)]
        simp only [integral_mul_const,compactMomentGram]

end ScalarConductivity

end

end OAI
