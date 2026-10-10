import Mathlib
import OAI.Probability.SKFluctuations.ProjectionRootEstimate

namespace OAI

/-! Scalar Clock Regularity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Set Filter GaussianCalculus
open scoped Topology NNReal BigOperators ContDiff

theorem scalarProfileJet_bddSmooth_all (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (t : ℝ≥0) (r k : ℕ) :
    BddSmooth r (fun x : Fin 1 → ℝ => scalarProfileJet α l t (k+1) (x 0)) := by
  induction r generalizing k with
  | zero => exact scalarProfileJet_bddSmooth α hα l t k
  | succ r ih =>
    refine ⟨ih k, fun v => ⟨fun y => v 0*scalarProfileJet α l t (k+2) (y 0),
      (ih (k+1)).const_mul (v 0), ?_⟩⟩
    intro x s
    have hh := scalarProfileJet_line α hα l t (k+1) x v s
    simpa only [Fin.sum_univ_one] using hh

private theorem ScalarClockRegularity_clockContinuation_scalar_source {F : (Fin 1 → ℝ) → ℝ}
    {G : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    {m : ℝ} (hm : m ≠ 0) (t x : ℝ) :
    HasDerivAt (fun y => clockContinuation m F t (fun _ => y))
      (clockTest m F (G 0) t (fun _ => x)) x := by
  have hdu (y : Fin 1 → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => F (y+r • (fun _ => 1)))
        (G 0 (y+s • (fun _ => 1))) s := by
    simpa only [Fin.sum_univ_one,one_mul] using hdF y (fun _ => 1) s
  have hh := hasDerivAt_clockContinuation_source hF (hG 0) hdu hm t (0 : Fin 1 → ℝ) x
  have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by
    ext i; simp
  simpa only [he] using hh

theorem clockContinuation_scalar_contDiffOn {F : (Fin 1 → ℝ) → ℝ}
    {G H : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F)
    (hG : ∀ k i, BddSmooth k (G i)) (hH : ∀ k i, BddSmooth k (H i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdG : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    ContDiffOn ℝ k (fun p : ℝ × ℝ => clockContinuation m F p.1 (fun _ => p.2))
      {p : ℝ × ℝ | 0 < p.1} := by
  cases k with
  | zero =>
    apply contDiffOn_zero.mpr
    exact ((clockContinuation_continuous hF m).comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))).continuousOn
  | succ k =>
    have htest : ∀ {A : (Fin 1 → ℝ) → ℝ}, (∀ r, BddSmooth r A) →
        ContDiffOn ℝ k (fun p : ℝ × ℝ => clockTest m F A p.1 (fun _ => p.2))
          {p : ℝ × ℝ | 0 < p.1} :=
      fun hA => clockTest_scalar_contDiffOn hF hG hH hdF hdG m k hA
    apply Scalar.contDiffOn_succ_of_partials
      (f := fun t x => clockContinuation m F t (fun _ => x))
      (S := {p : ℝ × ℝ | 0 < p.1})
      (f₁ := fun t x => clockDerivative m F G H t (fun _ => x))
      (f₂ := fun t x => clockTest m F (G 0) t (fun _ => x))
      (isOpen_lt continuous_const continuous_fst) k
    · intro p hp
      exact hasDerivAt_clockContinuation hF (hG 0) (hH 0) hdF hdG hm hp (fun _ => p.2)
    · intro p _
      exact ScalarClockRegularity_clockContinuation_scalar_source hF (hG 0) hdF hm.ne' p.1 p.2
    · have hsq : ∀ r, BddSmooth r (fun y => (G 0 y)^2) := by
        intro r
        simpa only [pow_two] using (hG r 0).mul (hG r 0)
      have hh := (contDiffOn_const (c := (1/2:ℝ))).mul ((htest (fun r => hH r 0)).add
        ((contDiffOn_const (c := m)).mul (htest hsq)))
      change ContDiffOn ℝ k (fun p : ℝ × ℝ => (1/2:ℝ)*
        ((∑ i : Fin 1, clockTest m F (H i) p.1 (fun _ => p.2))+
        m*∑ i : Fin 1, clockTest m F (fun y => (G i y)^2) p.1 (fun _ => p.2))) _
      simpa only [Fin.sum_univ_one] using hh
    · exact htest (fun r => hG r 0)

 

theorem scalarProfile_clock_contDiffOn (α : NonnegativeMassProfile)
    (hα : ∀ s, α.mass s ≤ 1) (l : ℝ) (T : ℝ≥0) {m : ℝ} (hm : 0 < m) (k : ℕ) :
    ContDiffOn ℝ k (fun p : ℝ × ℝ =>
      clockContinuation m (scalarProfileHeatJet α hα l T).F p.1 (fun _ => p.2))
      {p : ℝ × ℝ | 0 < p.1} :=
  clockContinuation_scalar_contDiffOn (scalarProfileHeatJet α hα l T).lipschitz
    (fun r _ => scalarProfileJet_bddSmooth_all α hα l T r 0)
    (fun r _ => scalarProfileJet_bddSmooth_all α hα l T r 1)
    (scalarProfileJet_line α hα l T 0) (scalarProfileJet_coord α hα l T 1) hm k

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

noncomputable def timePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (1,0)
noncomputable def spacePartial (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (0,1)

theorem hasDerivAt_timePartial {f : ℝ × ℝ → ℝ} {t x : ℝ}
    (hf : DifferentiableAt ℝ f (t,x)) :
    HasDerivAt (fun s => f (s,x)) (timePartial f (t,x)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem hasDerivAt_spacePartial {f : ℝ × ℝ → ℝ} {t x : ℝ}
    (hf : DifferentiableAt ℝ f (t,x)) :
    HasDerivAt (fun y => f (t,y)) (spacePartial f (t,x)) x := by
  exact hf.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

theorem timePartial_contDiffOn {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) {k : ℕ} (hf : ContDiffOn ℝ (k+1 : ℕ) f S) :
    ContDiffOn ℝ k (timePartial f) S := by
  exact (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

theorem spacePartial_contDiffOn {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) {k : ℕ} (hf : ContDiffOn ℝ (k+1 : ℕ) f S) :
    ContDiffOn ℝ k (spacePartial f) S := by
  exact (hf.fderiv_of_isOpen hS (by simp)).clm_apply contDiffOn_const

 
theorem hasDerivAt_spacePartial_time {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 2 f S) {t x : ℝ} (hp : (t,x) ∈ S) :
    HasDerivAt (fun s => spacePartial f (s,x))
      (spacePartial (timePartial f) (t,x)) t := by
  have hfa : ContDiffAt ℝ 2 f (t,x) := (hf (t,x) hp).contDiffAt (hS.mem_nhds hp)
  have hD := hf.fderiv_of_isOpen hS (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) (t,x) :=
    ((hD (t,x) hp).contDiffAt (hS.mem_nhds hp)).differentiableAt one_ne_zero
  have hs := hd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) (t,x))
  have ht := hd.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) (t,x))
  have hst := hs.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have he : spacePartial (timePartial f) (t,x) =
      fderiv ℝ (fderiv ℝ f) (t,x) (0,1) (1,0) := by
    change fderiv ℝ (fun q => fderiv ℝ f q (1,0)) (t,x) (0,1) = _
    rw [ht.fderiv]
    simp
  rw [he, ← hfa.isSymmSndFDerivAt (by norm_num) (1,0) (0,1)]
  convert hst using 1 <;> first | rfl | simp

end SKFluctuations.Scalar

 

 
namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

noncomputable def spatialJet (u : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => u
  | k+1 => spacePartial (spatialJet u k)

theorem spatialJet_contDiffOn {u : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hu : ∀ k : ℕ, ContDiffOn ℝ k u S) (r k : ℕ) :
    ContDiffOn ℝ k (spatialJet u r) S := by
  induction r generalizing k with
  | zero => exact hu k
  | succ r ih => exact spacePartial_contDiffOn hS (ih (k+1))

theorem spatialJet_hasDerivAt {u : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S) (hu : ∀ k : ℕ, ContDiffOn ℝ k u S)
    (r : ℕ) {t x : ℝ} (hp : (t,x) ∈ S) :
    HasDerivAt (fun y => spatialJet u r (t,y)) (spatialJet u (r+1) (t,x)) x := by
  apply hasDerivAt_spacePartial
  exact (((spatialJet_contDiffOn hS hu r 1) _ hp).contDiffAt (hS.mem_nhds hp)).differentiableAt one_ne_zero

 

theorem spacePartial_hasDerivAt_time_of_timePDE {u V : ℝ × ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u {p : ℝ × ℝ | 0 < p.1})
    (htime : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x)) (V (t,x)) t)
    {t x v : ℝ} (ht : 0 < t) (hV : HasDerivAt (fun y => V (t,y)) v x) :
    HasDerivAt (fun s => spacePartial u (s,x)) v t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have he : (fun y => timePartial u (t,y)) = fun y => V (t,y) := by
    funext y
    exact (hasDerivAt_timePartial (((hu _ ht).contDiffAt (hS.mem_nhds ht)).differentiableAt (by norm_num))).unique
      (htime t y ht)
  have hD : ContDiffOn ℝ 1 (timePartial u) {p : ℝ × ℝ | 0 < p.1} :=
    timePartial_contDiffOn hS hu
  have hh := hasDerivAt_spacePartial (((hD (t,x) ht).contDiffAt (hS.mem_nhds ht)).differentiableAt one_ne_zero)
  rw [he] at hh
  have hv := hh.unique hV
  exact hv ▸ hasDerivAt_spacePartial_time hS hu ht

 
theorem spatialJet_one_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => spatialJet u 1 (s,x))
      ((1/2:ℝ)*spatialJet u 3 (t,x)+m*spatialJet u 1 (t,x)*spatialJet u 2 (t,x)) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hd (r) := spatialJet_hasDerivAt hS hu r (x := x) ht
  have hh := ((hd 2).add (((hd 1).pow 2).const_mul m)).const_mul (1/2:ℝ)
  apply spacePartial_hasDerivAt_time_of_timePDE
    (V := fun p => (1/2:ℝ)*(spatialJet u 2 p+m*(spatialJet u 1 p)^2)) (hu 2) hPDE ht
  convert hh using 1
  first | rfl | ring

theorem spatialJet_two_timePDE {u : ℝ × ℝ → ℝ} {m : ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    (hPDE : ∀ t x, 0 < t → HasDerivAt (fun s => u (s,x))
      ((1/2:ℝ)*(spatialJet u 2 (t,x)+m*(spatialJet u 1 (t,x))^2)) t)
    {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => spatialJet u 2 (s,x))
      ((1/2:ℝ)*spatialJet u 4 (t,x)+m*((spatialJet u 2 (t,x))^2+
        spatialJet u 1 (t,x)*spatialJet u 3 (t,x))) t := by
  have hS : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hd (r) := spatialJet_hasDerivAt hS hu r (x := x) ht
  have hh := ((hd 3).const_mul (1/2:ℝ)).add (((hd 1).const_mul m).mul (hd 2))
  apply spacePartial_hasDerivAt_time_of_timePDE
    (V := fun p => (1/2:ℝ)*spatialJet u 3 p+m*spatialJet u 1 p*spatialJet u 2 p)
    (spatialJet_contDiffOn hS hu 1 2)
    (fun s y hs => spatialJet_one_timePDE hu hPDE (x := y) hs) ht
  convert hh using 1
  first | rfl | ring

end SKFluctuations.Scalar

 

 
namespace SKFluctuations.Hierarchy
open Set Filter GaussianCalculus
open scoped Topology ContDiff

theorem HeatJet.scalar_derivF (J : HeatJet 0) (x : ℝ) :
    HasDerivAt (fun y => J.F (fun _ => y)) (J.G 0 (fun _ => x)) x := by
  have hh := J.derivF (0 : Fin 1 → ℝ) (fun _ => 1) x
  have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by ext i; simp
  simpa only [he,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,one_mul] using hh

theorem HeatJet.scalar_derivG (J : HeatJet 0) (x : ℝ) :
    HasDerivAt (fun y => J.G 0 (fun _ => y)) (J.H 0 (fun _ => x)) x := by
  have hh := J.derivG 0 (0 : Fin 1 → ℝ) x
  have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • Pi.single 0 1 = fun _ => r := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  simpa only [he] using hh

noncomputable def HeatJet.scalarClockPlane (J : HeatJet 0) (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  clockContinuation m J.F p.1 (fun _ => p.2)

theorem HeatJet.scalarClockPlane_contDiffOn (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) (k : ℕ) :
    ContDiffOn ℝ k (J.scalarClockPlane m) {p : ℝ × ℝ | 0 < p.1} :=
  clockContinuation_scalar_contDiffOn J.lipschitz hG hH J.derivF J.derivG hm k

theorem HeatJet.scalarClockPlane_jet_one (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Scalar.spatialJet (J.scalarClockPlane m) 1 (t,x) = (J.evolve hm t).G 0 (fun _ => x) := by
  have ha := Scalar.spatialJet_hasDerivAt (isOpen_lt continuous_const continuous_fst)
    (J.scalarClockPlane_contDiffOn hG hH hm) 0 (x := x) ht
  exact ha.unique ((J.evolve hm t).scalar_derivF x)

theorem HeatJet.scalarClockPlane_jet_two (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Scalar.spatialJet (J.scalarClockPlane m) 2 (t,x) = (J.evolve hm t).H 0 (fun _ => x) := by
  have ha := Scalar.spatialJet_hasDerivAt (isOpen_lt continuous_const continuous_fst)
    (J.scalarClockPlane_contDiffOn hG hH hm) 1 (x := x) ht
  have he : (fun y => Scalar.spatialJet (J.scalarClockPlane m) 1 (t,y)) =
      fun y => (J.evolve hm t).G 0 (fun _ => y) :=
    funext (J.scalarClockPlane_jet_one hG hH hm ht)
  rw [he] at ha
  exact ha.unique ((J.evolve hm t).scalar_derivG x)

 
theorem HeatJet.scalarClockPlane_timePDE (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => J.scalarClockPlane m (s,x))
      ((1/2:ℝ)*(Scalar.spatialJet (J.scalarClockPlane m) 2 (t,x)+
        m*(Scalar.spatialJet (J.scalarClockPlane m) 1 (t,x))^2)) t := by
  rw [J.scalarClockPlane_jet_one hG hH hm ht,J.scalarClockPlane_jet_two hG hH hm ht]
  have hh := J.evolve_time_F hm ht (fun _ => x)
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hh
  convert hh using 1; rfl

theorem HeatJet.scalarClockPlane_gradient_timePDE (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => Scalar.spatialJet (J.scalarClockPlane m) 1 (s,x))
      ((1/2:ℝ)*Scalar.spatialJet (J.scalarClockPlane m) 3 (t,x)+
        m*Scalar.spatialJet (J.scalarClockPlane m) 1 (t,x)*
          Scalar.spatialJet (J.scalarClockPlane m) 2 (t,x)) t :=
  Scalar.spatialJet_one_timePDE (J.scalarClockPlane_contDiffOn hG hH hm)
    (fun _ y hs => J.scalarClockPlane_timePDE hG hH hm hs y) ht

theorem HeatJet.scalarClockPlane_curvature_timePDE (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) (hH : ∀ k i, BddSmooth k (J.H i))
    {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => Scalar.spatialJet (J.scalarClockPlane m) 2 (s,x))
      ((1/2:ℝ)*Scalar.spatialJet (J.scalarClockPlane m) 4 (t,x)+
        m*((Scalar.spatialJet (J.scalarClockPlane m) 2 (t,x))^2+
          Scalar.spatialJet (J.scalarClockPlane m) 1 (t,x)*
            Scalar.spatialJet (J.scalarClockPlane m) 3 (t,x))) t :=
  Scalar.spatialJet_two_timePDE (J.scalarClockPlane_contDiffOn hG hH hm)
    (fun _ y hs => J.scalarClockPlane_timePDE hG hH hm hs y) ht

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology

def SpatialRegular : ℕ → (ℝ × ℝ → ℝ) → Prop
  | 0,f => Continuous f
  | k+1,f => SpatialRegular k f ∧ ∃ g : ℝ × ℝ → ℝ,
      SpatialRegular k g ∧ ∀ t x, HasDerivAt (fun y => f (t,y)) (g (t,x)) x

namespace SpatialRegular

theorem const (k : ℕ) (c : ℝ) : SpatialRegular k (fun _ => c) := by
  induction k generalizing c with
  | zero => exact continuous_const
  | succ k ih => exact ⟨ih c,fun _ => 0,ih 0,fun _ _ => hasDerivAt_const _ _⟩

theorem add {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialRegular k f)
    (hg : SpatialRegular k g) : SpatialRegular k (fun p => f p+g p) := by
  induction k generalizing f g with
  | zero => exact Continuous.add hf hg
  | succ k ih =>
    obtain ⟨hf,f',hf',hdf⟩ := hf
    obtain ⟨hg,g',hg',hdg⟩ := hg
    exact ⟨ih hf hg,fun p => f' p+g' p,ih hf' hg',fun t x => (hdf t x).add (hdg t x)⟩

theorem mul {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialRegular k f)
    (hg : SpatialRegular k g) : SpatialRegular k (fun p => f p*g p) := by
  induction k generalizing f g with
  | zero => exact Continuous.mul hf hg
  | succ k ih =>
    obtain ⟨hf,f',hf',hdf⟩ := hf
    obtain ⟨hg,g',hg',hdg⟩ := hg
    exact ⟨ih hf hg,fun p => f' p*g p+f p*g' p,(ih hf' hg).add (ih hf hg'),
      fun t x => (hdf t x).mul (hdg t x)⟩

theorem const_mul {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialRegular k f) (c : ℝ) :
    SpatialRegular k (fun p => c*f p) := (const k c).mul hf

theorem neg {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialRegular k f) :
    SpatialRegular k (fun p => -f p) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

theorem sub {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialRegular k f)
    (hg : SpatialRegular k g) : SpatialRegular k (fun p => f p-g p) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem spatialDerivative {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialRegular (k+1) f) :
    SpatialRegular k (fun p : ℝ × ℝ => deriv (fun y => f (p.1,y)) p.2) := by
  obtain ⟨_,g,hg,hd⟩ := hf
  have he : (fun p : ℝ × ℝ => deriv (fun y => f (p.1,y)) p.2) = g := by
    funext p
    exact (hd p.1 p.2).deriv
  rw [he]
  exact hg

theorem hasDerivAt {f : ℝ × ℝ → ℝ} (hf : SpatialRegular 1 f) (t x : ℝ) :
    HasDerivAt (fun y => f (t,y)) (deriv (fun y => f (t,y)) x) x := by
  obtain ⟨_,g,_,hd⟩ := hf
  rw [(hd t x).deriv]
  exact hd t x

end SpatialRegular

noncomputable def realSpatialJet (f : ℝ × ℝ → ℝ) : ℕ → ℝ × ℝ → ℝ
  | 0 => f
  | k+1 => fun p => deriv (fun x => realSpatialJet f k (p.1,x)) p.2

theorem realSpatialJet_regular {f : ℝ × ℝ → ℝ} (hf : ∀ k, SpatialRegular k f) (n k : ℕ) :
    SpatialRegular k (realSpatialJet f n) := by
  induction n generalizing k with
  | zero => exact hf k
  | succ n ih => exact (ih (k+1)).spatialDerivative

theorem realSpatialJet_continuous {f : ℝ × ℝ → ℝ} (hf : ∀ k, SpatialRegular k f) (n : ℕ) :
    Continuous (realSpatialJet f n) := realSpatialJet_regular hf n 0

theorem realSpatialJet_hasDerivAt {f : ℝ × ℝ → ℝ} (hf : ∀ k, SpatialRegular k f)
    (n : ℕ) (t x : ℝ) :
    HasDerivAt (fun y => realSpatialJet f n (t,y)) (realSpatialJet f (n+1) (t,x)) x :=
  (realSpatialJet_regular hf n 1).hasDerivAt t x

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

private theorem ScalarClockSpatial_test_source_all {F A : (Fin 1 → ℝ) → ℝ}
    {G A₁ : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    (hG : ∀ i, BddSmooth 0 (G i)) (hA₁ : ∀ i, BddSmooth 0 (A₁ i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hdA : ∀ x v t, HasDerivAt (fun s : ℝ => A (x+s • v))
      (∑ i, v i*A₁ i (x+t • v)) t)
    (m t x : ℝ) :
    HasDerivAt (fun y => clockTest m F A t (fun _ => y))
      (clockGradient m F (G 0) A (A₁ 0) t (fun _ => x)) x := by
  have hh := hasDerivAt_clockTest_source_vector hF hA hG hA₁ hdF hdA m t
    (0 : Fin 1 → ℝ) (fun _ => 1) x
  have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by ext i; simp
  simp only [he] at hh
  change HasDerivAt (fun y => clockTest m F A t (fun _ => y))
    (∑ i : Fin 1, 1*clockGradient m F (G i) A (A₁ i) t (fun _ => x)) x at hh
  simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,one_mul] using hh

theorem clockTest_scalar_spatialRegular {F : (Fin 1 → ℝ) → ℝ}
    {G : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ k i, BddSmooth k (G i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (m : ℝ) (k : ℕ) {A : (Fin 1 → ℝ) → ℝ} (hA : ∀ r, BddSmooth r A) :
    Scalar.SpatialRegular k (fun p : ℝ × ℝ => clockTest m F A p.1 (fun _ => p.2)) := by
  induction k generalizing A with
  | zero =>
    exact (clockTest_continuous hF (hA 0) m).comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))
  | succ k ih =>
    let A₁ : Fin 1 → (Fin 1 → ℝ) → ℝ := fun i y => lineDeriv ℝ A y (Pi.single i 1)
    have hs₁ (r i) : BddSmooth r (A₁ i) := (hA (r+1)).lineDeriv_smooth _
    refine ⟨ih hA,fun p => clockGradient m F (G 0) A (A₁ 0) p.1 (fun _ => p.2),?_,?_⟩
    · exact (ih (fun r => hs₁ r 0)).add
        (((ih fun r => (hA r).mul (hG r 0)).sub ((ih hA).mul (ih fun r => hG r 0))).const_mul m)
    · intro t x
      exact ScalarClockSpatial_test_source_all hF (hA 0) (hG 0) (hs₁ 0) hdF (fun x v s => by
        have hh := (hA 1).hasDerivAt_line x v s
        rw [(hA 1).lineDeriv_pi] at hh
        exact hh) m t x

theorem HeatJet.scalarClockPlane_spatialRegular (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m) (k : ℕ) :
    Scalar.SpatialRegular k (J.scalarClockPlane m) := by
  induction k with
  | zero =>
    exact (clockContinuation_continuous J.lipschitz m).comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd))
  | succ k ih =>
    refine ⟨ih,fun p => (J.evolve hm p.1).G 0 (fun _ => p.2),?_,?_⟩
    · exact clockTest_scalar_spatialRegular J.lipschitz hG J.derivF m k (fun r => hG r 0)
    · intro t x
      exact (J.evolve hm t).scalar_derivF x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Scalar
open Set Filter
open scoped Topology ContDiff

theorem realSpatialJet_eq_spatialJet {u : ℝ × ℝ → ℝ}
    (hu : ∀ k : ℕ, ContDiffOn ℝ k u {p : ℝ × ℝ | 0 < p.1})
    {t : ℝ} (ht : 0 < t) (n : ℕ) (x : ℝ) :
    realSpatialJet u n (t,x) = spatialJet u n (t,x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change deriv (fun y => realSpatialJet u n (t,y)) x = _
    simp_rw [ih]
    exact (spatialJet_hasDerivAt (isOpen_lt continuous_const continuous_fst) hu n (x := x) ht).deriv

end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar
open SKFluctuations.Hierarchy

def SpatialBounded : ℕ → (ℝ × ℝ → ℝ) → Prop
  | 0,f => Continuous f ∧ AbsBounded f
  | k+1,f => SpatialBounded k f ∧ ∃ g : ℝ × ℝ → ℝ,
      SpatialBounded k g ∧ ∀ t x, HasDerivAt (fun y => f (t,y)) (g (t,x)) x

namespace SpatialBounded

theorem const (k : ℕ) (c : ℝ) : SpatialBounded k (fun _ => c) := by
  induction k generalizing c with
  | zero => exact ⟨continuous_const,|c|,abs_nonneg c,fun _ => le_rfl⟩
  | succ k ih => exact ⟨ih c,fun _ => 0,ih 0,fun _ _ => hasDerivAt_const _ _⟩

theorem add {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialBounded k f)
    (hg : SpatialBounded k g) : SpatialBounded k (fun p => f p+g p) := by
  induction k generalizing f g with
  | zero => exact ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  | succ k ih =>
    obtain ⟨hf,f',hf',hdf⟩ := hf
    obtain ⟨hg,g',hg',hdg⟩ := hg
    exact ⟨ih hf hg,fun p => f' p+g' p,ih hf' hg',fun t x => (hdf t x).add (hdg t x)⟩

theorem mul {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialBounded k f)
    (hg : SpatialBounded k g) : SpatialBounded k (fun p => f p*g p) := by
  induction k generalizing f g with
  | zero => exact ⟨hf.1.mul hg.1,hf.2.mul hg.2⟩
  | succ k ih =>
    obtain ⟨hf,f',hf',hdf⟩ := hf
    obtain ⟨hg,g',hg',hdg⟩ := hg
    exact ⟨ih hf hg,fun p => f' p*g p+f p*g' p,(ih hf' hg).add (ih hf hg'),
      fun t x => (hdf t x).mul (hdg t x)⟩

theorem const_mul {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialBounded k f) (c : ℝ) :
    SpatialBounded k (fun p => c*f p) := (const k c).mul hf

theorem neg {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialBounded k f) :
    SpatialBounded k (fun p => -f p) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

theorem sub {k : ℕ} {f g : ℝ × ℝ → ℝ} (hf : SpatialBounded k f)
    (hg : SpatialBounded k g) : SpatialBounded k (fun p => f p-g p) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem spatialDerivative {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialBounded (k+1) f) :
    SpatialBounded k (fun p : ℝ × ℝ => deriv (fun y => f (p.1,y)) p.2) := by
  obtain ⟨_,g,hg,hd⟩ := hf
  have he : (fun p : ℝ × ℝ => deriv (fun y => f (p.1,y)) p.2) = g := by
    funext p
    exact (hd p.1 p.2).deriv
  rw [he]
  exact hg

theorem regular {k : ℕ} {f : ℝ × ℝ → ℝ} (hf : SpatialBounded k f) : SpatialRegular k f := by
  induction k generalizing f with
  | zero => exact hf.1
  | succ k ih =>
    obtain ⟨hf,g,hg,hd⟩ := hf
    exact ⟨ih hf,g,ih hg,hd⟩

end SpatialBounded

theorem realSpatialJet_spatialBounded {f : ℝ × ℝ → ℝ} (hf : ∀ k, SpatialBounded k f) (n k : ℕ) :
    SpatialBounded k (realSpatialJet f n) := by
  induction n generalizing k with
  | zero => exact hf k
  | succ n ih => exact (ih (k+1)).spatialDerivative

theorem bddSmooth_of_uniform_real_chain {u : ℕ → ℝ × ℝ → ℝ}
    (hc : ∀ n, Continuous (u n)) (hb : ∀ n, AbsBounded (u n))
    (hd : ∀ n t x, HasDerivAt (fun y => u n (t,y)) (u (n+1) (t,x)) x)
    (r n : ℕ) (t : ℝ) : BddSmooth r (fun x : Fin 1 → ℝ => u n (t,x 0)) := by
  induction r generalizing n with
  | zero =>
    obtain ⟨K,hK,hb⟩ := hb n
    exact ⟨(hc n).comp (continuous_const.prodMk (continuous_apply 0)),K,hK,fun x => hb (t,x 0)⟩
  | succ r ih =>
    refine ⟨ih n,fun v => ⟨fun y => v 0*u (n+1) (t,y 0),(ih (n+1)).const_mul (v 0),?_⟩⟩
    intro x s
    have hh := (hd n t (x 0+s*v 0)).comp s
      (((hasDerivAt_id s).mul_const (v 0)).const_add (x 0))
    convert hh using 1 <;> first | rfl | (simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring)

end SKFluctuations.Scalar

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators

theorem clockTest_scalar_spatialBounded {F : (Fin 1 → ℝ) → ℝ}
    {G : Fin 1 → (Fin 1 → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ k i, BddSmooth k (G i))
    (hdF : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (m : ℝ) (k : ℕ) {A : (Fin 1 → ℝ) → ℝ} (hA : ∀ r, BddSmooth r A) :
    Scalar.SpatialBounded k (fun p : ℝ × ℝ => clockTest m F A p.1 (fun _ => p.2)) := by
  induction k generalizing A with
  | zero =>
    obtain ⟨K,hK,hb⟩ := clockTest_absBounded hF (hA 0) m
    exact ⟨(clockTest_continuous hF (hA 0) m).comp
      (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd)),K,hK,fun p => hb (p.1,fun _ => p.2)⟩
  | succ k ih =>
    let A₁ : Fin 1 → (Fin 1 → ℝ) → ℝ := fun i y => lineDeriv ℝ A y (Pi.single i 1)
    have hs₁ (r i) : BddSmooth r (A₁ i) := (hA (r+1)).lineDeriv_smooth _
    refine ⟨ih hA,fun p => clockGradient m F (G 0) A (A₁ 0) p.1 (fun _ => p.2),?_,?_⟩
    · exact (ih (fun r => hs₁ r 0)).add
        (((ih fun r => (hA r).mul (hG r 0)).sub ((ih hA).mul (ih fun r => hG r 0))).const_mul m)
    · intro t x
      have hh := hasDerivAt_clockTest_source_vector hF (hA 0) (hG 0) (hs₁ 0) hdF
        (fun y v s => by
          have hh := (hA 1).hasDerivAt_line y v s
          rw [(hA 1).lineDeriv_pi] at hh
          exact hh) m t (0 : Fin 1 → ℝ) (fun _ => 1) x
      have he (r : ℝ) : (0 : Fin 1 → ℝ)+r • (fun _ => 1) = fun _ => r := by ext i; simp
      simp only [he] at hh
      change HasDerivAt (fun y => clockTest m F A t (fun _ => y))
        (∑ i : Fin 1, 1*clockGradient m F (G i) A (A₁ i) t (fun _ => x)) x at hh
      simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,one_mul] using hh

theorem HeatJet.scalarClockPlane_positiveJets_uniformBounded (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m) (n : ℕ) :
    AbsBounded (Scalar.realSpatialJet (J.scalarClockPlane m) (n+1)) := by
  have hd (t x) := (J.evolve hm t).scalar_derivF x
  have he : Scalar.realSpatialJet (J.scalarClockPlane m) 1 =
      fun p => clockTest m J.F (J.G 0) p.1 (fun _ => p.2) := by
    funext p
    exact (hd p.1 p.2).deriv
  have hj (n : ℕ) : Scalar.realSpatialJet (J.scalarClockPlane m) (n+1) =
      Scalar.realSpatialJet (fun p => clockTest m J.F (J.G 0) p.1 (fun _ => p.2)) n := by
    induction n with
    | zero => exact he
    | succ n ih =>
      change (fun p : ℝ × ℝ => deriv (fun x => Scalar.realSpatialJet (J.scalarClockPlane m) (n+1) (p.1,x)) p.2) = _
      rw [ih]
      rfl
  rw [hj]
  exact (Scalar.realSpatialJet_spatialBounded
    (fun k => clockTest_scalar_spatialBounded J.lipschitz hG J.derivF m k (fun r => hG r 0)) n 0).2

theorem HeatJet.scalarClockPlane_positiveJets_bddSmooth (J : HeatJet 0)
    (hG : ∀ k i, BddSmooth k (J.G i)) {m : ℝ} (hm : 0 < m) (r n : ℕ) (t : ℝ) :
    BddSmooth r (fun x : Fin 1 → ℝ => Scalar.realSpatialJet (J.scalarClockPlane m) (n+1) (t,x 0)) := by
  apply Scalar.bddSmooth_of_uniform_real_chain
    (u := fun n => Scalar.realSpatialJet (J.scalarClockPlane m) (n+1))
  · intro k
    exact Scalar.realSpatialJet_continuous (J.scalarClockPlane_spatialRegular hG hm) (k+1)
  · intro k
    exact J.scalarClockPlane_positiveJets_uniformBounded hG hm k
  · intro k s x
    exact Scalar.realSpatialJet_hasDerivAt (J.scalarClockPlane_spatialRegular hG hm) (k+1) s x

end SKFluctuations.Hierarchy

end

end OAI
