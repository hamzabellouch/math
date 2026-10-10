import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Covariance

namespace OAI

/-! Connections for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterWindowLaw
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterWindow (G : BondGraph V E) (x : V) (lo hi : ℕ) (ω : Set E) : Prop :=
  (cluster G ω x).Finite ∧ lo ≤ (cluster G ω x).ncard ∧ (cluster G ω x).ncard < hi

theorem clusterWindow_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) (ω : Set E) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
    ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E)) := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  change ClusterWindow G x lo hi ω ↔ ClusterWindow G x lo hi (ω ∩ (Q : Set E))
  constructor
  · rintro ⟨hf,hl,hh⟩
    have hs : cluster G ω x ⊆ (finite_reachBall hloc x hi).toFinset := by
      simpa only [Set.Finite.coe_toFinset] using finite_cluster_subset_reachBall G ω x hf hi hh.le
    have he := cluster_restrict_incident_of_full G hloc _ ω x hs
    change cluster G (ω ∩ (Q : Set E)) x = cluster G ω x at he
    exact ⟨he.symm ▸ hf,he.symm ▸ hl,he.symm ▸ hh⟩
  · rintro ⟨hf,hl,hh⟩
    have he := cluster_restrict_of_cap G hloc Q ω x hi (Finset.Subset.refl _) hf hh.le
    exact ⟨he ▸ hf,he ▸ hl,he ▸ hh⟩

theorem measurableSet_clusterWindow (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (lo hi : ℕ) : MeasurableSet {ω | ClusterWindow G x lo hi ω} := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  have he : {ω | ClusterWindow G x lo hi ω} =
      {ω | ω ∩ (Q : Set E) ∈ {η | ClusterWindow G x lo hi η}} := by
    ext ω
    exact clusterWindow_local G hloc x lo hi ω
  rw [he]
  exact measurableSet_finite_restriction Q _

noncomputable def clusterWindowProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : ℝ := (law p).real {ω | ClusterWindow G x lo hi ω}

theorem finiteClusterWindowMass_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (p : unitInterval) (x : V) (lo hi : ℕ)
    (hQ : incidentSupport G hloc (finite_reachBall hloc x hi).toFinset ⊆ Q) :
    finiteClusterWindowMass G Q p x lo hi = clusterWindowProbability G p x lo hi := by
  let S := incidentSupport G hloc (finite_reachBall hloc x hi).toFinset
  let f : Set E → ℝ := fun ω => if ClusterWindow G x lo hi ω then 1 else 0
  have hf (ω) : f ω = f (ω ∩ (S : Set E)) :=
    if_congr (clusterWindow_local G hloc x lo hi ω) rfl rfl
  have he := integral_finite_local Q p f (finite_local_of_subset S Q hQ f hf)
  trans ∫ ω, f ω ∂law p
  · rw [he]
    unfold finiteClusterWindowMass finiteFieldIntegral
    apply Finset.sum_congr rfl
    intro η _
    congr 1
    unfold f ClusterWindow
    dsimp only
    split_ifs <;> rfl
  change (∫ ω, ({η | ClusterWindow G x lo hi η}.indicator (1 : Set E → ℝ)) ω ∂law p) = _
  exact integral_indicator_one (measurableSet_clusterWindow G hloc x lo hi)

theorem clusterWindowProbability_nonneg (G : BondGraph V E) (p : unitInterval)
    (x : V) (lo hi : ℕ) : 0 ≤ clusterWindowProbability G p x lo hi := ENNReal.toReal_nonneg

theorem clusterWindowProbability_mono (G : BondGraph V E) (p : unitInterval)
    (x : V) {a b c d : ℕ} (hac : c ≤ a) (hbd : b ≤ d) :
    clusterWindowProbability G p x a b ≤ clusterWindowProbability G p x c d := by
  apply measureReal_mono
  · intro ω h
    exact ⟨h.1,hac.trans h.2.1,h.2.2.trans_le hbd⟩
  · exact measure_ne_top _ _

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem finiteClusterWindowMass_amplification (o : V)
    (q : LocalEndpointRule G hloc (vertexOrbit G o) M L) (k n : ℕ) (p : unitInterval) (x : V) :
    finiteClusterWindowMass G (q.amplificationBonds k n x) p x (n-k*M) (2*n) =
      clusterWindowProbability G p x (n-k*M) (2*n) := by
  apply finiteClusterWindowMass_eq G hloc
  exact incidentSupport_ball_mono G hloc x (by dsimp [amplificationRadius]; omega)

end LocalEndpointRule
end ClusterWindowLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def amplificationMomentFactor (k M d : ℕ) (c a t : ℝ) : ℝ :=
  4 + (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ) + (2*c*(k*M:ℕ))^2*t/a

theorem amplificationMomentFactor_pos (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    0 < amplificationMomentFactor k M d c a t := by
  unfold amplificationMomentFactor
  positivity

namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem amplificationLoad_moment_factor [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (a t π : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 ≤ π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k) :
    (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p) ≤
      amplificationMomentFactor k M d c a t * q.successProbability p (root i₀)^k *
        (q.successProbability p (root i₀)^k * binOrbitRow G p (root i₀) n / n) := by
  let u := q.successProbability p (root i₀)
  let B := u^k * binOrbitRow G p (root i₀) n / n
  let D : ℝ := (((k*M)+(k*M)^2+d*(k*M)^3:ℕ):ℝ)
  have hu : 0 ≤ u^k := pow_nonneg (q.successProbability_nonneg p _) _
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin hu
  have hB0 : 0 ≤ B := (mul_nonneg (mul_nonneg ha.le hπ) hu).trans hB
  have hcoef : 4*u^k+D*inverseCodeMass M L^k/n ≤ (4+D)*u^k := by
    have h := mul_le_mul_of_nonneg_left hcode (show 0 ≤ D by positivity)
    have h' : D*inverseCodeMass M L^k/n ≤ D*u^k := by
      apply (div_le_iff₀ hn').mpr
      nlinarith only [h]
    nlinarith only [h']
  have hrem : (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) ≤
      ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := by
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ ((2*c*(k*M:ℕ))^2*t/a)*u^k from
        mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) ht) ha.le) hu)
    calc
      _ = (((2*c*(k*M:ℕ))^2*t/a)*u^k)*(a*π*u^k) := by
        field_simp
      _ ≤ _ := h
  have hself : root i₀ ∈ vertexOrbit G (root i₀) := by
    refine ⟨Equiv.refl V,Equiv.refl E,?_,rfl⟩
    intro e
    simp
  have he := q.amplificationLoad_mean root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n (root i₀) hself
  have hm := q.amplificationLoad_second_moment_le hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p (root i₀) k n d hn hdeg
  rw [he,q.finiteClusterWindowMass_amplification] at hm
  change _ ≤ (4*u^k+D*inverseCodeMass M L^k/n)*B +
    (2*(c*((k*M:ℕ)*u^k)))^2*clusterWindowProbability G p (root i₀) (n-k*M) (2*n) at hm
  calc
    _ ≤ _ := hm
    _ ≤ (4+D)*u^k*B + (2*(c*((k*M:ℕ)*u^k)))^2*(t*π) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hB0)
        (mul_le_mul_of_nonneg_left hwindow (sq_nonneg _))
    _ ≤ (4+D)*u^k*B + ((2*c*(k*M:ℕ))^2*t/a)*u^k*B := add_le_add (le_refl _) hrem
    _ = _ := by dsimp [amplificationMomentFactor,D,B,u]; ring

end LocalEndpointRule
end QuantitativeAmplificationMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section QuantitativeAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem quantitative_amplification_step [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a t π L' : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 < π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k)
    (hbad : 16*amplificationMomentFactor k M d c a t *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ a*π)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      a*π/(8*amplificationMomentFactor k M d c a t) ≤ q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  let Q := amplificationMomentFactor k M d c a t
  let u := q.successProbability p (root i₀)
  let B := u^k*binOrbitRow G p (root i₀) n / n
  let b := 4*Q*u^k
  have hQ : 0 < Q := amplificationMomentFactor_pos k M d c a t ha ht
  have huk : 0 < u^k := pow_pos hu _
  have hb : 0 < b := mul_pos (mul_pos (by norm_num) hQ) huk
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hbin0 : 0 < binOrbitRow G p (root i₀) n :=
    (mul_pos (mul_pos ha hn') hπ).trans_le hbin
  have hB : a*π*u^k ≤ B := by
    apply (le_div_iff₀ hn').mpr
    calc
      _ = u^k*(a*n*π) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbin huk.le
  have hm := q.amplificationLoad_moment_factor hconn root weight Γ hΓ htr hcov hw hw1
    c hc hmin i₀ hw₀ hL p k n d hn hdeg a t π ha ht hπ.le hbin hwindow hcode
  have hmoment : (∫ ω, (q.amplificationLoad (root i₀) hL k n p).row ω (root i₀)^2 ∂law p)/b ≤ B/4 := by
    apply (div_le_iff₀ hb).mpr
    change _ ≤ Q*u^k*B at hm
    calc
      _ ≤ Q*u^k*B := hm
      _ = _ := by dsimp [b]; ring
  have hbad' : b*(law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ B/4 := by
    have hh := mul_le_mul_of_nonneg_right hbad huk.le
    dsimp [b]
    nlinarith only [hh,hB]
  obtain ⟨q',hq',A',hA'pos,hA'norm,hA'⟩ := q.amplification_truncation_step root weight Γ htr
    (fun e he => hΓ he) hw i₀ hw₀ hL p k n hn hu hbin0 b L' hb hmoment hbad' A hA
  refine ⟨q',?_,A',hA'pos,hA'norm,hA'⟩
  apply le_trans _ hq'
  change a*π/(8*Q) ≤ B/(2*b)
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hQ) (mul_pos (by norm_num) hb)).mpr
  have hh := mul_le_mul_of_nonneg_left hB (show 0 ≤ 8*Q by positivity)
  dsimp [b]
  nlinarith only [hh]

end LocalEndpointRule
end QuantitativeAmplificationStep
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedRule
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def cappedConnectionMass (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : ℝ :=
  if CappedGoodness G ω x M L ∧ Conn G ω x y then c*S x y/twoPoint G p x y else 0

theorem cappedConnectionMass_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c) (hS : ∀ x y, 0 ≤ S x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : 0 ≤ cappedConnectionMass G p S c M L ω x y := by
  unfold cappedConnectionMass
  split_ifs
  · exact div_nonneg (mul_nonneg hc (hS x y)) (twoPoint_nonneg G p x y)
  · rfl

theorem cappedConnectionMass_support (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V)
    (h : cappedConnectionMass G p S c M L ω x y ≠ 0) :
    S x y ≠ 0 ∧ CappedGoodness G ω x M L ∧ Conn G ω x y := by
  unfold cappedConnectionMass at h
  split_ifs at h with hh
  · refine ⟨?_,hh⟩
    intro hz
    simp only [hz,mul_zero,zero_div] at h
    exact h rfl
  · exact (h rfl).elim

theorem cappedConnectionMass_le (G : BondGraph V E) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) : cappedConnectionMass G p S c M L ω x y ≤ S x y := by
  by_cases hs : S x y = 0
  · simp only [cappedConnectionMass,hs,mul_zero,zero_div,ite_self,le_refl]
  · unfold cappedConnectionMass
    split_ifs
    · apply (div_le_iff₀ (hc.trans_le (hτ x y hs))).mpr
      exact (mul_le_mul_of_nonneg_right (hτ x y hs) (hS x y)).trans_eq (mul_comm _ _)
    · exact hS x y

theorem cappedConnectionMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (ω : Set E) (x y : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
    cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y := by
  let Q := incidentSupport G hloc (finite_reachBall hloc x M).toFinset
  change cappedConnectionMass G p S c M L ω x y = cappedConnectionMass G p S c M L (ω ∩ (Q:Set E)) x y
  have hg := cappedGoodness_local G hloc ω x M L
  change CappedGoodness G ω x M L ↔ CappedGoodness G (ω ∩ (Q:Set E)) x M L at hg
  unfold cappedConnectionMass
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h,hxy⟩
    have h' := hg.mp h
    have he := cluster_restrict_of_cap G hloc Q ω x M (Finset.Subset.refl _) h'.1 h'.2.1
    refine ⟨h',?_⟩
    change y ∈ cluster G (ω ∩ (Q:Set E)) x
    rw [he]
    exact hxy
  · rintro ⟨h,hxy⟩
    exact ⟨hg.mpr h,conn_mono G Set.inter_subset_left hxy⟩

theorem cappedConnectionMass_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ)
    (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b)
    (hS : ∀ x y, S (a x) (a y) = S x y) (ω : Set E) (x y : V) :
    cappedConnectionMass G p S c M L (b ⁻¹' ω) x y = cappedConnectionMass G p S c M L ω (a x) (a y) := by
  simp only [cappedConnectionMass,cappedGoodness_aut_iff G hab,conn_aut_iff G hab,
    hS,twoPoint_aut G p hab]

noncomputable def connectionAdjustedRule [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ O ∧ y ∈ O)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L : ℝ) : LocalEndpointRule G hloc O M L where
  mass := cappedConnectionMass G p S c M L
  radius := M
  nonneg := cappedConnectionMass_nonneg G p S c hc.le hS M L
  support := by
    intro ω x y h
    obtain ⟨hs,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y h
    exact ⟨(hO x y hs).1,(hO x y hs).2,hxy,hg⟩
  locality := fun ω x y => cappedConnectionMass_local G hloc p S c M L ω x y
  covariance := fun a b hab ω x y => cappedConnectionMass_covariant G p S c M L a b hab (hcov a b hab) ω x y
  row_le_one := by
    intro ω x
    have hs : Summable (cappedConnectionMass G p S c M L ω x) := by
      apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x M).toFinset)
      intro y hy
      by_contra hn
      obtain ⟨_,hg,hxy⟩ := cappedConnectionMass_support G p S c M L ω x y hn
      apply hy
      simp only [Set.Finite.mem_toFinset]
      exact finite_cluster_subset_reachBall G ω x hg.1 M hg.2.1 hxy
    exact (hs.tsum_le_tsum (cappedConnectionMass_le G p S c hc hS hτ M L ω x) (hSsum x)).trans (hrow x)

end ConnectionAdjustedRule

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedKernel
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

theorem integral_cappedConnectionMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (M : ℕ) (L : ℝ) (x y : V) :
    (∫ ω, cappedConnectionMass G p S c M L ω x y ∂law p) =
      c*S x y/twoPoint G p x y * (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} := by
  have hm : MeasurableSet {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} :=
    (measurableSet_capped_good G hloc x M L).inter (measurableSet_conn G x y)
  simpa only [cappedConnectionMass,Set.indicator,Set.mem_ofPred_eq,smul_eq_mul,mul_comm] using
    integral_indicator_const (μ := law p) (c*S x y/twoPoint G p x y) hm

theorem integral_cappedConnectionMass_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (M : ℕ) (L : ℝ) (x y : V) :
    let K := ∫ ω, cappedConnectionMass G p S c M L ω x y ∂law p
    K ≤ c*S x y ∧ c*S x y ≤ K + S x y * (law p).real {ω | ¬ CappedGoodness G ω x M L} := by
  dsimp only
  rw [integral_cappedConnectionMass G hloc]
  by_cases hs : S x y = 0
  · simp only [hs,mul_zero,zero_div,zero_mul,zero_add,le_refl,and_self]
  have ht : 0 < twoPoint G p x y := hc.trans_le (hτ x y hs)
  let a := c*S x y/twoPoint G p x y
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hc.le (hS x y)) ht.le
  have hle : a ≤ S x y := by
    apply (div_le_iff₀ ht).mpr
    exact (mul_le_mul_of_nonneg_right (hτ x y hs) (hS x y)).trans_eq (mul_comm _ _)
  have he : a*twoPoint G p x y = c*S x y := div_mul_cancel₀ _ ht.ne'
  have hsub : {ω : Set E | CappedGoodness G ω x M L ∧ Conn G ω x y} ⊆ {ω | Conn G ω x y} :=
    fun _ h => h.2
  have hm : (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} ≤ twoPoint G p x y := by
    exact measureReal_mono hsub (measure_ne_top _ _)
  have hcover : {ω : Set E | Conn G ω x y} ⊆
      {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} ∪ {ω | ¬ CappedGoodness G ω x M L} := by
    intro ω h
    by_cases hg : CappedGoodness G ω x M L
    · exact Or.inl ⟨hg,h⟩
    · exact Or.inr hg
  have hb : twoPoint G p x y ≤
      (law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
        (law p).real {ω | ¬ CappedGoodness G ω x M L} :=
    (measureReal_mono hcover (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  constructor
  · exact (mul_le_mul_of_nonneg_left hm ha).trans_eq he
  · calc
      c*S x y = a*twoPoint G p x y := he.symm
      _ ≤ a*((law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
          (law p).real {ω | ¬ CappedGoodness G ω x M L}) := mul_le_mul_of_nonneg_left hb ha
      _ ≤ a*(law p).real {ω | CappedGoodness G ω x M L ∧ Conn G ω x y} +
          S x y*(law p).real {ω | ¬ CappedGoodness G ω x M L} := by
        rw [mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hle measureReal_nonneg)

 

theorem connectionAdjustedRule_success_lower
    (G : BondGraph V E) (hloc : LocallyFinite G) (O : Set V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ O ∧ y ∈ O)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L : ℝ) (x : V) :
    c*(∑' y, S x y) ≤
      (connectionAdjustedRule G hloc O p S c hc hS hSsum hrow hτ hO hcov M L).successProbability p x +
        (law p).real {ω | ¬ CappedGoodness G ω x M L} := by
  let q := connectionAdjustedRule G hloc O p S c hc hS hSsum hrow hτ hO hcov M L
  let ε := (law p).real {ω | ¬ CappedGoodness G ω x M L}
  have h (y : V) : c*S x y ≤ q.kernel p x y + S x y * ε :=
    (integral_cappedConnectionMass_bounds G hloc p S c hc hS hτ M L x y).2
  have hh := ((hSsum x).mul_left c).tsum_le_tsum h
    ((q.summable_kernel p x).add ((hSsum x).mul_right ε))
  rw [(q.summable_kernel p x).tsum_add ((hSsum x).mul_right ε),tsum_mul_left,tsum_mul_right] at hh
  exact hh.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_right (hrow x) measureReal_nonneg).trans_eq (one_mul ε)))

end ConnectionAdjustedKernel

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionAdjustedOperator
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

 

theorem connectionAdjustedRule_operator
    (G : BondGraph V E) (hloc : LocallyFinite G) (o : V) (p : unitInterval)
    (S : V → V → ℝ) (c : ℝ) (hc : 0 < c) (hS : ∀ x y, 0 ≤ S x y)
    (hSsum : ∀ x, Summable (S x)) (hrow : ∀ x, ∑' y, S x y ≤ 1)
    (hτ : ∀ x y, S x y ≠ 0 → c ≤ twoPoint G p x y)
    (hO : ∀ x y, S x y ≠ 0 → x ∈ vertexOrbit G o ∧ y ∈ vertexOrbit G o)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, S (a x) (a y) = S x y)
    (M : ℕ) (L b : ℝ) (hb : 0 < b) (hret : b ≤ ∑' y, S o y)
    (hbad : (law p).real {ω | ¬ CappedGoodness G ω o M L} ≤ c*b/2)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (S x y : ℂ)) :
    ∃ q : LocalEndpointRule G hloc (vertexOrbit G o) M L,
      c*b/2 ≤ q.successProbability p o ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ ≤ 2*‖A‖/b ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel o p x y : ℂ) := by
  let q := connectionAdjustedRule G hloc (vertexOrbit G o) p S c hc hS hSsum hrow hτ hO hcov M L
  have hlo := connectionAdjustedRule_success_lower G hloc (vertexOrbit G o) p S c hc hS hSsum hrow hτ hO hcov M L o
  have hs : c*b/2 ≤ q.successProbability p o := by
    have hmul := mul_le_mul_of_nonneg_left hret hc.le
    change _ ≤ q.successProbability p o + _ at hlo
    linarith
  have hu : 0 < q.successProbability p o := (by positivity : 0 < c*b/2).trans_le hs
  have hcA (x y : V) : matrixCoeff ((c:ℂ) • A) x y = (c*S x y : ℝ) := by
    change (c:ℂ)*matrixCoeff A x y = _
    rw [hA,Complex.ofReal_mul]
  obtain ⟨B,hBn,hB⟩ := exists_operator_of_matrix_domination
    (fun x y => c*S x y) (q.kernel p) (fun x y => mul_nonneg hc.le (hS x y))
    (fun x y => by
      rw [abs_of_nonneg (q.kernel_nonneg p x y)]
      exact (integral_cappedConnectionMass_bounds G hloc p S c hc hS hτ M L x y).1)
    ((c:ℂ) • A) hcA
  have hBn' : ‖B‖ ≤ c*‖A‖ := by
    simpa only [norm_smul,Complex.norm_of_nonneg hc.le] using hBn
  obtain ⟨T,hTn,hT⟩ := q.normalize_mass_operator o p hu B _ hBn' hB
  refine ⟨q,hs,T,q.normalized_operator_norm_pos o p hu T hT,hTn.trans ?_,hT⟩
  apply (div_le_iff₀ hu).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2*‖A‖ by positivity)
  nlinarith only [hh]

end ConnectionAdjustedOperator

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter Real
open scoped Topology
section CappedGoodnessLimit
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E]

omit [Countable V] in
theorem clusterLarge_probability_tendsto_zero (G : BondGraph V E) (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    Tendsto (fun M : ℕ => (law p).real (clusterLarge G x M)) atTop (𝓝 0) := by
  have hz : law p {ω | (cluster G ω x).Infinite} = 0 := by
    simpa only [Set.Infinite] using (ae_iff.mp hfin)
  have ht := (ENNReal.tendsto_toReal (measure_ne_top (law p) (⋂ M, clusterLarge G x M))).comp
    (tendsto_measure_iInter_atTop (fun M => (measurableSet_clusterLarge G x M).nullMeasurableSet)
      (clusterLarge_antitone G x) ⟨0,measure_ne_top _ _⟩)
  rw [← infinite_cluster_eq_iInter,hz,ENNReal.toReal_zero] at ht
  exact ht

omit [Countable V] [Countable E] in
theorem cappedGoodness_failure_le (G : BondGraph V E) (p : unitInterval)
    (x : V) (M : ℕ) (L : ℝ) :
    (law p).real {ω | ¬ CappedGoodness G ω x M L} ≤
      (law p).real (clusterLarge G x M) + (law p).real {ω | CappedBadGoodness G ω x M L} := by
  have hsub : {ω : Set E | ¬ CappedGoodness G ω x M L} ⊆
      clusterLarge G x M ∪ {ω | CappedBadGoodness G ω x M L} := by
    intro ω hbad
    by_cases hf : (cluster G ω x).Finite
    · by_cases hM : (cluster G ω x).ncard ≤ M
      · exact Or.inr ⟨hf,hM,fun hg => hbad ⟨hf,hM,hg⟩⟩
      · apply Or.inl
        refine ⟨hf.toFinset,?_,fun y hy => hf.mem_toFinset.mp hy⟩
        rw [← Set.ncard_eq_toFinset_card _ hf]
        omega
    · obtain ⟨t,ht,hcard⟩ := (show (cluster G ω x).Infinite from hf).exists_subset_card_eq M
      exact Or.inl ⟨t,hcard.ge,ht⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)

omit [Countable V] in
 

theorem cappedGoodness_failure_eventually_small [Nonempty V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : (p:ℝ) < 1) (x : V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, (law p).real {ω | ¬ CappedGoodness G ω x M ((M:ℝ)^(1/2+ε))} ≤ δ := by
  have htail := (clusterLarge_probability_tendsto_zero G p x hfin).eventually
    (Iio_mem_nhds (show (0:ℝ) < δ/2 by positivity))
  have hr : Tendsto (fun M : ℕ => (M:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun M : ℕ => Real.exp (-(M:ℝ)^ε)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hr)
  have he := hexp.eventually (Iio_mem_nhds (show (0:ℝ) < δ/2 by positivity))
  filter_upwards [htail,he,bad_goodness_stretched_exp G hloc hqt p hp ε hε hε1] with M ht he hg
  have hbad := hg x p le_rfl
  have hle := cappedGoodness_failure_le G p x M ((M:ℝ)^(1/2+ε))
  linarith

end CappedGoodnessLimit

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkPowerSupport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem walkKernel_zero_of_not_step (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) (hxy : x ≠ y) (hadj : ¬ Adj G x y) :
    walkKernel G hloc a x y = 0 := by simp only [walkKernel,ite_eq_right hxy,ite_eq_right hadj,zero_add]

theorem walkKernel_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ) (x : V) :
    HasSum (walkKernel G hloc a x) 1 := by
  rw [← walkKernel_row_sum G hloc a x]
  apply hasSum_sum_of_ne_finset_zero
  intro y hy
  simp only [Finset.mem_insert,mem_neighbors,not_or] at hy
  exact walkKernel_zero_of_not_step G hloc a x y (Ne.symm hy.1) hy.2

theorem walkPower_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x y : V) (hy : y ∉ reachBall G x k) : (matrixCoeff (P^k) x y).re = 0 := by
  induction k generalizing y with
  | zero =>
    have he : y ≠ x := by simpa only [reachBall,Set.mem_singleton_iff] using hy
    simp only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,ite_eq_right (Ne.symm he),Complex.zero_re]
  | succ k ih =>
    rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
    rw [← tsum_zero]
    apply tsum_congr
    intro z
    by_cases hz : z ∈ reachBall G x k
    · have hzy : z ≠ y := by intro he; subst y; exact hy (Or.inl hz)
      have hadj : ¬ Adj G z y := by
        intro h
        apply hy
        apply Or.inr
        simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
        exact ⟨z,hz,h⟩
      rw [hP,walkKernel_zero_of_not_step G hloc a z y hzy hadj,Complex.ofReal_zero,Complex.zero_re,mul_zero]
    · rw [ih z hz,zero_mul]

theorem walkPower_hasSum (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (k : ℕ) (x : V) : HasSum (fun y => (matrixCoeff (P^k) x y).re) 1 := by
  induction k with
  | zero =>
    have h : HasSum (fun y : V => if x=y then (1:ℝ) else 0) 1 := by
      exact hasSum_ite_eq' x (1:ℝ)
    simpa only [pow_zero,matrixCoeff,one_apply_eq_self,lp.single_apply,Pi.single_apply,apply_ite,Complex.one_re,Complex.zero_re] using h
  | succ k ih =>
    let B := (finite_reachBall hloc x k).toFinset
    have he (y : V) : (matrixCoeff (P^(k+1)) x y).re =
        ∑ z ∈ B, (matrixCoeff (P^k) x z).re * walkKernel G hloc a z y := by
      rw [pow_succ,← ((hpos.pow k).mul_hasSum P x y).tsum_eq]
      simp only [hP,Complex.ofReal_re]
      apply tsum_eq_sum
      intro z hz
      rw [walkPower_support G hloc a P hpos hP k x z (by simpa only [B,Set.Finite.mem_toFinset] using hz),zero_mul]
    have hs := hasSum_sum (s := B) (fun z _ => (walkKernel_hasSum G hloc a z).mul_left (matrixCoeff (P^k) x z).re)
    simp only [mul_one] at hs
    have hr : (∑ z ∈ B, (matrixCoeff (P^k) x z).re) = 1 := by
      rw [← ih.tsum_eq]
      exact (tsum_eq_sum fun z hz => walkPower_support G hloc a P hpos hP k x z
        (by simpa only [B,Set.Finite.mem_toFinset] using hz)).symm
    simpa only [← he,hr] using hs

end WalkPowerSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkCovariance
attribute [local instance] Classical.propDecidable Classical.decEq

theorem neighbors_aut_card (G : BondGraph V E) (hloc : LocallyFinite G)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x : V) :
    (neighbors G hloc (g x)).card = (neighbors G hloc x).card := by
  have he : neighbors G hloc (g x) = (neighbors G hloc x).map g.toEmbedding := by
    ext y
    simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
    constructor
    · intro h
      refine ⟨g.symm y,?_,by simp⟩
      simpa only [g.symm_apply_apply] using adj_aut G (isAut_symm G hg) h
    · rintro ⟨z,hz,rfl⟩
      exact adj_aut G hg hz
  rw [he,Finset.card_map]

theorem walkKernel_covariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {g : V ≃ V} {b : E ≃ E} (hg : IsAut G g b) (x y : V) :
    walkKernel G hloc a (g x) (g y) = walkKernel G hloc a x y := by
  have hadj : Adj G (g x) (g y) ↔ Adj G x y :=
    ⟨fun h => by simpa using adj_aut G (isAut_symm G hg) h,adj_aut G hg⟩
  simp only [walkKernel,g.apply_eq_iff_eq,neighbors_aut_card G hloc hg,hadj]

theorem twoPoint_reachBall_lower [Countable E] (G : BondGraph V E) (p : unitInterval)
    (x : V) (k : ℕ) (y : V) (hy : y ∈ reachBall G x k) :
    (p:ℝ)^k ≤ twoPoint G p x y := by
  induction k generalizing y with
  | zero =>
    simp only [reachBall,Set.mem_singleton_iff] at hy
    subst y
    simp only [pow_zero,twoPoint_self,le_refl]
  | succ k ih =>
    rcases hy with hy | hy
    · have h : (p:ℝ)^(k+1) ≤ (p:ℝ)^k := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg p.2.1 k) p.2.2
      exact h.trans (ih y hy)
    · simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hy
      obtain ⟨z,hz,hzy⟩ := hy
      have h := mul_le_mul_of_nonneg_left (ih z hz) p.2.1
      rw [←pow_succ'] at h
      exact h.trans (twoPoint_adj_lower G p x z y hzy)

end WalkCovariance
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

lemma finiteKernel_summable_mul (K : V → V → ℝ)
    (hf : ∀ x, (Function.support (K x)).Finite) (x : V) (f : V → ℝ) :
    Summable (fun y => K x y * f y) := by
  apply summable_of_ne_finset_zero (s := (hf x).toFinset)
  intro y hy
  have hd : K x y = 0 := by simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hy
  rw [hd,zero_mul]

 

theorem orbit_two_step_return_lower (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (K : V → V → ℝ)
    (hfin : ∀ x, (Function.support (K x)).Finite)
    (hrow : ∀ x, HasSum (K x) 1) (hsym : ∀ x y, K x y = K y x)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' z, K (root i₀) z * ∑' y, if y ∈ vertexOrbit G (root i₀) then K z y else 0 := by
  let O := vertexOrbit G (root i₀)
  let I : V → ℝ := fun x => if x ∈ O then 1 else 0
  let f : V → ℝ := fun x => ∑' y, K x y * I y
  let g : V → ℝ := fun x => ∑' y, K x y * f y
  let σ := ∑ i, weight i * I (root i)
  have hI (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : I (a x) = I x := by
    simp only [I,O,mem_vertexOrbit_aut_iff G (root i₀) hab]
  have hf (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : f (a x) = f x := by
    dsimp only [f]
    rw [←a.tsum_eq (fun y => K (a x) y*I y)]
    simp only [hcov a b hab,hI a b hab]
  have hg (a : V ≃ V) (b : E ≃ E) (hab : IsAut G a b) (x : V) : g (a x) = g x := by
    dsimp only [g]
    rw [←a.tsum_eq (fun y => K (a x) y*f y)]
    simp only [hcov a b hab,hf a b hab]
  have hgO (x : V) (hx : x ∈ O) : g x = g (root i₀) := by
    obtain ⟨a,b,hab,rfl⟩ := hx
    exact hg a b hab _
  have hmean : ∑ i, weight i*f (root i) = σ := by
    have ht := htr.real root weight Γ (fun x y => K x y*I y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab])
      (fun x => finiteKernel_summable_mul K hfin x I)
      (fun y => by simpa only [hsym, mul_comm] using (hrow y).summable.mul_left (I y))
    calc
      _ = ∑ i, weight i * ∑' x, K x (root i)*I (root i) := ht
      _ = σ := by simp only [tsum_mul_right,show ∀ y, ∑' x, K x y = 1 from fun y => by simpa only [hsym] using (hrow y).tsum_eq,one_mul,σ]
  have hsecond : σ*g (root i₀) = ∑ i, weight i*f (root i)^2 := by
    have ht := htr.real root weight Γ (fun x y => I x*K x y*f y)
      (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; rw [hcov a b hab,hI a b hab,hf a b hab])
      (fun x => by simpa only [mul_assoc] using (finiteKernel_summable_mul K hfin x f).mul_left (I x))
      (fun y => by simpa only [hsym,mul_comm,mul_left_comm,mul_assoc] using (finiteKernel_summable_mul K hfin y I).mul_right (f y))
    have hr (i : ι) : I (root i)*g (root i) = I (root i)*g (root i₀) := by
      by_cases hi : root i ∈ O
      · rw [hgO _ hi]
      · simp only [I,ite_eq_right hi,zero_mul]
    calc
      _ = ∑ i, weight i*(I (root i)*g (root i)) := by
        simp only [hr,σ,Finset.sum_mul,mul_assoc]
      _ = ∑ i, weight i*∑' x, I x*K x (root i)*f (root i) := by
        simpa only [mul_assoc,tsum_mul_left,g] using ht
      _ = ∑ i, weight i*f (root i)^2 := by
        simp only [tsum_mul_right]
        congr 1
        ext i
        congr 1
        rw [show (∑' x, I x*K x (root i)) = f (root i) by simp only [f,hsym,mul_comm]]
        ring
  have hvariance : 0 ≤ ∑ i, weight i*(f (root i)-σ)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have he : (∑ i, weight i*(f (root i)-σ)^2) = (∑ i, weight i*f (root i)^2)-σ^2 := by
    simp_rw [sub_sq,mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hc : (∑ i, weight i*(2*f (root i)*σ)) = 2*σ*(∑ i, weight i*f (root i)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    rw [hc,hmean,←Finset.sum_mul,hw1,one_mul]
    ring
  rw [he,←hsecond] at hvariance
  have hσ : 0 < σ := by
    have hx : root i₀ ∈ O := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
    have hIn (x : V) : 0 ≤ I x := by dsimp [I]; split_ifs <;> norm_num
    have hb := Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (hIn (root i))) (Finset.mem_univ i₀)
    have he₀ : weight i₀*I (root i₀) = weight i₀ := by simp only [I,ite_eq_left hx,mul_one]
    rw [he₀] at hb
    exact hw₀.trans_le hb
  have hbound : σ ≤ g (root i₀) := by nlinarith only [hvariance,hσ]
  simpa only [σ,g,f,I,mul_ite,mul_one,mul_zero,zero_mul] using hbound

end OrbitReturn
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WalkOrbitReturn
attribute [local instance] Classical.propDecidable Classical.decEq

theorem matrixCoeff_real_symm (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : IsSelfAdjoint A) (x y : V) : (matrixCoeff A x y).re = (matrixCoeff A y x).re := by
  have h := congrArg Complex.re (matrixCoeff_adjoint A x y)
  simpa only [hA.star_eq,Complex.star_def,Complex.conj_re] using h

theorem finite_positive_square_row (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : PositiveRealMatrix A) (hfin : ∀ x, (Function.support (fun y => (matrixCoeff A x y).re)).Finite)
    (f : V → ℝ) (x : V) :
    (∑' y, (matrixCoeff (A*A) x y).re*f y) =
      ∑' z, (matrixCoeff A x z).re*∑' y, (matrixCoeff A z y).re*f y := by
  let K := fun x y => (matrixCoeff A x y).re
  let B := (hfin x).toFinset
  have hz (z : V) (hz : z ∉ B) : K x z = 0 := by
    simpa only [B,Set.Finite.mem_toFinset,Function.mem_support,not_not] using hz
  have he (y : V) : (matrixCoeff (A*A) x y).re*f y = ∑ z ∈ B, K x z*(K z y*f y) := by
    rw [←(hA.mul_hasSum A x y).tsum_eq,tsum_eq_sum (s := B) (fun z h => by change K x z*K z y = 0; rw [hz z h,zero_mul]),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z h
    exact mul_assoc _ _ _
  have hs := hasSum_sum (s := B) (fun z _ =>
    (finiteKernel_summable_mul K hfin z f).hasSum.mul_left (K x z))
  have hr : (∑' z, K x z*∑' y, K z y*f y) = ∑ z ∈ B, K x z*∑' y, K z y*f y :=
    tsum_eq_sum (fun z h => by rw [hz z h,zero_mul])
  simpa only [←he,←hr] using hs.tsum_eq

theorem walkPower_finite_support (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) (x : V) :
    (Function.support (fun y => (matrixCoeff (P^k) x y).re)).Finite := by
  apply (finite_reachBall hloc x k).subset
  intro y hy
  by_contra hn
  exact hy (walkPower_support G hloc a P hpos hP k x y hn)

theorem walkPower_invariant (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    KernelInvariant (vertexAut G) (P^k) := by
  apply KernelInvariant.pow
  intro g hg x y
  obtain ⟨b,hb⟩ := hg
  simp only [hP,walkKernel_covariant G hloc a hb]

 

theorem walkPower_even_orbit_return (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ)) (k : ℕ) :
    (∑ i, if root i ∈ vertexOrbit G (root i₀) then weight i else 0) ≤
      ∑' y, if y ∈ vertexOrbit G (root i₀) then (matrixCoeff (P^(2*k)) (root i₀) y).re else 0 := by
  have h := orbit_two_step_return_lower G root weight Γ hΓ htr hw hw1 i₀ hw₀
    (fun x y => (matrixCoeff (P^k) x y).re)
    (walkPower_finite_support G hloc a P hpos hP k)
    (walkPower_hasSum G hloc a P hpos hP k)
    (matrixCoeff_real_symm (P^k) (hsym.pow k))
    (fun g b hb x y => congrArg Complex.re (walkPower_invariant G hloc a P hP k g ⟨b,hb⟩ x y))
  have he := finite_positive_square_row (P^k) (hpos.pow k)
    (walkPower_finite_support G hloc a P hpos hP k)
    (fun y => if y ∈ vertexOrbit G (root i₀) then 1 else 0) (root i₀)
  simp only [mul_ite,mul_one,mul_zero] at he
  rw [←he] at h
  simpa only [←pow_add,←two_mul] using h

end WalkOrbitReturn
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped Topology
section StartingEndpointRule
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem starting_endpoint_rule_of_walk (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (a : ℝ) (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hsym : IsSelfAdjoint P) (hnorm : ‖P‖ < 1)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (η : ℝ) (hη : 0 < η) (M₀ : ℕ) :
    ∃ M ≥ M₀, ∃ q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M ((M:ℝ)^(1/2+ε)),
      0 < q.successProbability p (root i₀) ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ < η ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  let O := vertexOrbit G (root i₀)
  have ho : root i₀ ∈ O := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  let b : ℝ := ∑ i, if root i ∈ O then weight i else 0
  have hb : 0 < b := by
    have hn (i : ι) : 0 ≤ if root i ∈ O then weight i else 0 := by split_ifs; exact hw i; exact le_rfl
    have hh := Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ i₀)
    simp only [ite_eq_left ho] at hh
    exact hw₀.trans_le hh
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg P) hnorm
  obtain ⟨k,hk⟩ := (ht.eventually (Iio_mem_nhds (show (0:ℝ) < η*b/2 by positivity))).exists
  have hk1 : ‖P‖^k ≤ 1 := pow_le_one₀ (norm_nonneg P) hnorm.le
  have hk2 : 2*‖P‖^(2*k)/b < η := by
    rw [show 2*k = k+k from Nat.two_mul k,pow_add]
    have hh : ‖P‖^k*‖P‖^k ≤ ‖P‖^k := mul_le_of_le_one_right (pow_nonneg (norm_nonneg P) _) hk1
    apply (div_lt_iff₀ hb).mpr
    change ‖P‖^k < η*b/2 at hk
    nlinarith only [hh,hk]
  let K : V → V → ℝ := fun x y => (matrixCoeff (P^(2*k)) x y).re
  let S : V → V → ℝ := fun x y => if x ∈ O ∧ y ∈ O then K x y else 0
  have hK (x y : V) : 0 ≤ K x y := (hpos.pow (2*k) x y).2
  have hS (x y : V) : 0 ≤ S x y := by dsimp [S]; split_ifs; exact hK x y; exact le_rfl
  have hSK (x y : V) : S x y ≤ K x y := by dsimp [S]; split_ifs; exact le_rfl; exact hK x y
  have hsum (x : V) : HasSum (K x) 1 := walkPower_hasSum G hloc a P hpos hP (2*k) x
  have hSsum (x : V) : Summable (S x) := Summable.of_nonneg_of_le (hS x) (hSK x) (hsum x).summable
  have hrow (x : V) : ∑' y, S x y ≤ 1 := by
    rw [←(hsum x).tsum_eq]
    exact (hSsum x).tsum_le_tsum (hSK x) (hsum x).summable
  have hτ (x y : V) (hxy : S x y ≠ 0) : (p:ℝ)^(2*k) ≤ twoPoint G p x y := by
    apply twoPoint_reachBall_lower G p x (2*k) y
    by_contra hn
    have hz := walkPower_support G hloc a P hpos hP (2*k) x y hn
    apply hxy
    dsimp [S,K]
    rw [hz]
    split_ifs <;> rfl
  have hO (x y : V) (hxy : S x y ≠ 0) : x ∈ O ∧ y ∈ O := by
    by_contra ho
    exact hxy (ite_eq_right ho)
  have hcov (g : V ≃ V) (d : E ≃ E) (hg : IsAut G g d) (x y : V) : S (g x) (g y) = S x y := by
    simp only [S,O,mem_vertexOrbit_aut_iff G (root i₀) hg,K,
      walkPower_invariant G hloc a P hP (2*k) g ⟨d,hg⟩]
  have hret : b ≤ ∑' y, S (root i₀) y := by
    simpa only [b,S,K,ho,true_and,O] using
      walkPower_even_orbit_return G hloc a root weight Γ hΓ htr hw hw1 i₀ hw₀ P hpos hsym hP k
  obtain ⟨A,hAn,hA⟩ := exists_operator_of_matrix_domination K S hK
    (fun x y => by rw [abs_of_nonneg (hS x y)]; exact hSK x y) (P^(2*k)) (hpos.pow (2*k)).real
  have hc : 0 < (p:ℝ)^(2*k) := pow_pos hp _
  have hbad := cappedGoodness_failure_eventually_small G hloc hqt p hp1 (root i₀) hfin ε hε hε1
    ((p:ℝ)^(2*k)*b/2) (by positivity)
  obtain ⟨M,hM,hMb⟩ := ((eventually_ge_atTop M₀).and hbad).exists
  obtain ⟨q,hq,T,hTpos,hTn,hT⟩ := connectionAdjustedRule_operator G hloc (root i₀) p S
    ((p:ℝ)^(2*k)) hc hS hSsum hrow hτ hO hcov M ((M:ℝ)^(1/2+ε)) b hb hret hMb A hA
  refine ⟨M,hM,q,(by positivity : 0 < (p:ℝ)^(2*k)*b/2).trans_le hq,T,hTpos,?_,hT⟩
  apply lt_of_le_of_lt hTn
  apply lt_of_le_of_lt _ hk2
  have hpow (j : ℕ) : ‖P^j‖ ≤ ‖P‖^j := by
    induction j with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ j ih =>
      rw [pow_succ,pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hAn.trans (hpow (2*k))) (by norm_num)) hb.le

end StartingEndpointRule
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section NonamenableStartingMap
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem nonamenable_starting_endpoint_rule (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (η : ℝ) (hη : 0 < η) (M₀ : ℕ) :
    ∃ M ≥ M₀, ∃ q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M ((M:ℝ)^(1/2+ε)),
      0 < q.successProbability p (root i₀) ∧
      ∃ T : Hilbert V →L[ℂ] Hilbert V, 0 < ‖T‖ ∧ ‖T‖ < η ∧
        ∀ x y, matrixCoeff T x y = (q.normalizedKernel (root i₀) p x y : ℂ) := by
  obtain ⟨D,P,hD,hdeg,hPn,hPs,hP⟩ := exists_strict_walk_operator G hloc hqt hh
  have hDr : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have ha : 0 ≤ (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hpos : PositiveRealMatrix P := by
    intro x y
    change (P (lp.single 2 y (1:ℂ)) x).im = 0 ∧ 0 ≤ (P (lp.single 2 y (1:ℂ)) x).re
    rw [hP]
    exact ⟨Complex.ofReal_im _,walkKernel_nonneg G hloc D hdeg _ ha haD x y⟩
  exact starting_endpoint_rule_of_walk G hloc hqt p hp hp1 root weight Γ hΓ htr hw hw1 i₀ hw₀ hfin
    _ P hpos hPs.isSelfAdjoint hPn hP ε hε hε1 η hη M₀

end NonamenableStartingMap
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteOrbitPartition
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_partition_square_bound {α ι : Type*} [Fintype ι]
    (C : Finset α) (color : α → ι) (q : α → ℝ)
    (hq : ∀ x ∈ C, (∑ y ∈ C, if color y = color x then (1:ℝ) else 0) ≤ q x) :
    (C.card:ℝ)^2 ≤ Fintype.card ι * ∑ x ∈ C, q x := by
  let c : ι → ℝ := fun i => ∑ x ∈ C, if color x=i then 1 else 0
  have hsum : (∑ i, c i) = C.card := by
    dsimp only [c]
    rw [Finset.sum_comm]
    simp
  have hsq : (∑ i, c i^2) = ∑ x ∈ C, c (color x) := by
    have he (i : ι) : c i^2 = ∑ x ∈ C, if color x=i then c i else 0 := by
      rw [pow_two]
      conv_lhs => lhs; change ∑ x ∈ C, if color x=i then (1:ℝ) else 0
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp only [one_mul,zero_mul]
    simp only [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1:ℝ)) c
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hsum,hsq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq) (Nat.cast_nonneg _))

theorem vertexOrbit_eq_of_mem (G : BondGraph V E) (o x : V) (hx : x ∈ vertexOrbit G o) :
    vertexOrbit G x = vertexOrbit G o := by
  obtain ⟨a,b,hab,rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.trans c,b.trans d,isAut_trans G hab hcd,hc⟩
  · rintro ⟨c,d,hcd,hc⟩
    exact ⟨a.symm.trans c,b.symm.trans d,isAut_trans G (isAut_symm G hab) hcd,by simpa using hc⟩

 

theorem finite_sameOrbit_pairs_lower (G : BondGraph V E)
    {ι : Type*} [Fintype ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (C : Finset V) :
    (C.card:ℝ)^2 ≤ Fintype.card ι *
      ∑ x ∈ C, ∑ y ∈ C, if y ∈ vertexOrbit G x then (1:ℝ) else 0 := by
  let color : V → ι := fun x => (hcover x).choose
  have hc (x : V) : x ∈ vertexOrbit G (root (color x)) := (hcover x).choose_spec
  apply finite_partition_square_bound C color
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  by_cases h : color y = color x
  · have hm : y ∈ vertexOrbit G x := by
      rw [vertexOrbit_eq_of_mem G (root (color x)) x (hc x)]
      simpa only [h] using hc y
    simp only [ite_eq_left h,ite_eq_left hm,le_refl]
  · simp only [ite_eq_right h]
    split_ifs <;> norm_num

end FiniteOrbitPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinOrbitRowMass
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binSizeMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, binConnectionMass G n ω x y

noncomputable def binOrbitRowMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) : ℝ :=
  ∑' y, if y ∈ vertexOrbit G x then binConnectionMass G n ω x y else 0

theorem binMass_eq_of_window (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hb : ClusterWindow G x n (2*n) ω) :
    binConnectionMass G n ω x y = if y ∈ cluster G ω x then 1 else 0 := by
  simp only [binConnectionMass,hb.1,hb.2.1,hb.2.2,true_and]
  rfl

theorem binMass_zero_of_not_window (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hb : ¬ ClusterWindow G x n (2*n) ω) : binConnectionMass G n ω x y = 0 := by
  apply ite_eq_right
  exact fun h => hb ⟨h.1,h.2.1,h.2.2.1⟩

theorem binSizeMass_eq (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ClusterWindow G x n (2*n) ω) : binSizeMass G n ω x = (cluster G ω x).ncard := by
  unfold binSizeMass
  simp only [binMass_eq_of_window G n ω x _ hb]
  rw [tsum_eq_sum (s := hb.1.toFinset) (fun y hy => by simp only [Set.Finite.mem_toFinset] at hy; simp only [ite_eq_right hy])]
  have he : (∑ y ∈ hb.1.toFinset, if y ∈ cluster G ω x then (1:ℝ) else 0) = ∑ _y ∈ hb.1.toFinset, (1:ℝ) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact ite_eq_left (hb.1.mem_toFinset.mp hy)
  rw [he]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hb.1]

theorem binOrbitRowMass_eq (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ClusterWindow G x n (2*n) ω) :
    binOrbitRowMass G n ω x = ∑ y ∈ hb.1.toFinset, if y ∈ vertexOrbit G x then (1:ℝ) else 0 := by
  unfold binOrbitRowMass
  rw [tsum_eq_sum (s := hb.1.toFinset) (fun y hy => by
    have hc : y ∉ cluster G ω x := fun h => hy (hb.1.mem_toFinset.mpr h)
    rw [binMass_eq_of_window G n ω x y hb,ite_eq_right hc,ite_self])]
  apply Finset.sum_congr rfl
  intro y hy
  rw [binMass_eq_of_window G n ω x y hb,ite_eq_left (hb.1.mem_toFinset.mp hy)]

theorem binOrbitRowMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V) :
    0 ≤ binOrbitRowMass G n ω x := by
  apply tsum_nonneg
  intro y
  split_ifs
  · exact binConnectionMass_nonneg G n ω x y
  · exact le_rfl

theorem binOrbitRowMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binOrbitRowMass G n ω x = binOrbitRowMass G n (ω ∩ (Q : Set E)) x := by
  dsimp only [binOrbitRowMass]
  apply tsum_congr
  intro y
  rw [binConnectionMass_local G hloc n ω x y]

theorem binSizeMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x : V) :
    let Q := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    binSizeMass G n ω x = binSizeMass G n (ω ∩ (Q : Set E)) x := by
  dsimp only [binSizeMass]
  apply tsum_congr
  intro y
  exact binConnectionMass_local G hloc n ω x y

theorem binOrbitRowMass_covariant (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    binOrbitRowMass G n (b ⁻¹' ω) x = binOrbitRowMass G n ω (a x) := by
  unfold binOrbitRowMass
  rw [←a.tsum_eq (fun y => if y ∈ vertexOrbit G (a x) then binConnectionMass G n ω (a x) y else 0)]
  have ho : vertexOrbit G (a x) = vertexOrbit G x := vertexOrbit_eq_of_mem G x (a x) ⟨a,b,hab,rfl⟩
  simp only [ho,mem_vertexOrbit_aut_iff G x hab,binConnectionMass_covariant G hab]

theorem binSizeMass_covariant (G : BondGraph V E) (n : ℕ) (ω : Set E)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    binSizeMass G n (b ⁻¹' ω) x = binSizeMass G n ω (a x) := by
  unfold binSizeMass
  rw [←a.tsum_eq (fun y => binConnectionMass G n ω (a x) y)]
  simp only [binConnectionMass_covariant G hab]

end BinOrbitRowMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binOrbitTransportMass (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) : ℝ :=
  binConnectionMass G n ω x y * binOrbitRowMass G n ω y / binSizeMass G n ω x

theorem binOrbitRowMass_zero (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hb : ¬ ClusterWindow G x n (2*n) ω) : binOrbitRowMass G n ω x = 0 := by
  simp only [binOrbitRowMass,binMass_zero_of_not_window G n ω x _ hb,ite_self,tsum_zero]

theorem binOrbitTransportMass_nonneg (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V) :
    0 ≤ binOrbitTransportMass G n ω x y := by
  exact div_nonneg (mul_nonneg (binConnectionMass_nonneg G n ω x y) (binOrbitRowMass_nonneg G n ω y))
    (tsum_nonneg (binConnectionMass_nonneg G n ω x))

theorem binOrbitTransportMass_column (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (ω : Set E) (y : V) : (∑' x, binOrbitTransportMass G n ω x y) = binOrbitRowMass G n ω y := by
  by_cases hb : ClusterWindow G y n (2*n) ω
  · have he (x : V) : binOrbitTransportMass G n ω x y =
        binConnectionMass G n ω x y * (binOrbitRowMass G n ω y / binSizeMass G n ω y) := by
      by_cases hz : binConnectionMass G n ω x y = 0
      · simp only [binOrbitTransportMass,hz,zero_mul,zero_div]
      · obtain ⟨hf,hN,hc⟩ := binConnectionMass_support G n ω x y hz
        have hset := cluster_eq_of_conn G ω hc
        have hbx : ClusterWindow G x n (2*n) ω := by
          unfold ClusterWindow at hb ⊢
          simpa only [hset] using hb
        rw [binOrbitTransportMass,binSizeMass_eq G n ω x hbx,binSizeMass_eq G n ω y hb,hset]
        exact mul_div_assoc _ _ _
    rw [show (∑' x, binOrbitTransportMass G n ω x y) =
      ∑' x, binConnectionMass G n ω x y*(binOrbitRowMass G n ω y/binSizeMass G n ω y) from tsum_congr he,
      tsum_mul_right]
    have hcol : (∑' x, binConnectionMass G n ω x y) = binSizeMass G n ω y := by
      simp only [binConnectionMass_symm G n ω,binSizeMass]
    rw [hcol]
    have hs : binSizeMass G n ω y ≠ 0 := by
      rw [binSizeMass_eq G n ω y hb]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hn.trans_le hb.2.1))
    exact mul_div_cancel₀ _ hs
  · have he : ∀ x, binOrbitTransportMass G n ω x y = 0 := by
      intro x
      simp only [binOrbitTransportMass,binOrbitRowMass_zero G n ω y hb,mul_zero,zero_div]
    simp only [he,tsum_zero,binOrbitRowMass_zero G n ω y hb]

theorem binOrbitTransportMass_row (G : BondGraph V E)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (n : ℕ) (hn : 0 < n) (ω : Set E) (x : V) :
    (if ClusterWindow G x n (2*n) ω then (n:ℝ)/Fintype.card ι else 0) ≤
      ∑' y, binOrbitTransportMass G n ω x y := by
  by_cases hb : ClusterWindow G x n (2*n) ω
  · rw [ite_eq_left hb]
    let C := hb.1.toFinset
    have hs : (0:ℝ) < (cluster G ω x).ncard := Nat.cast_pos.mpr (hn.trans_le hb.2.1)
    have ht : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have hqy (y : V) (hy : y ∈ C) : binOrbitRowMass G n ω y =
        ∑ z ∈ C, if z ∈ vertexOrbit G y then (1:ℝ) else 0 := by
      have hc : Conn G ω x y := hb.1.mem_toFinset.mp hy
      have he := cluster_eq_of_conn G ω hc
      have hby : ClusterWindow G y n (2*n) ω := by
        unfold ClusterWindow at hb ⊢
        simpa only [←he] using hb
      rw [binOrbitRowMass_eq G n ω y hby]
      have hC : hby.1.toFinset = C := by
        apply Finset.coe_injective
        simpa only [C,Set.Finite.coe_toFinset] using he.symm
      rw [hC]
    have he : (∑' y, binOrbitTransportMass G n ω x y) =
        (∑ y ∈ C, ∑ z ∈ C, if z ∈ vertexOrbit G y then (1:ℝ) else 0)/(cluster G ω x).ncard := by
      rw [tsum_eq_sum (s := C) (fun y hy => by
        have hc : y ∉ cluster G ω x := fun h => hy (hb.1.mem_toFinset.mpr h)
        simp only [binOrbitTransportMass,binMass_eq_of_window G n ω x y hb,ite_eq_right hc,zero_mul,zero_div])]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [binOrbitTransportMass,binMass_eq_of_window G n ω x y hb,
        ite_eq_left (hb.1.mem_toFinset.mp hy),one_mul,binSizeMass_eq G n ω x hb,hqy y hy]
    rw [he]
    apply (div_le_div_iff₀ ht hs).mpr
    have h := finite_sameOrbit_pairs_lower G root hcover C
    have hC : (C.card:ℝ) = (cluster G ω x).ncard := by
      exact_mod_cast (Set.ncard_eq_toFinset_card _ hb.1).symm
    rw [hC] at h
    have hn' : (n:ℝ) ≤ (cluster G ω x).ncard := by exact_mod_cast hb.2.1
    nlinarith [mul_le_mul_of_nonneg_right hn' hs.le]
  · rw [ite_eq_right hb]
    exact tsum_nonneg (binOrbitTransportMass_nonneg G n ω x)

end BinOrbitTransport

end Percolation

end OAI
