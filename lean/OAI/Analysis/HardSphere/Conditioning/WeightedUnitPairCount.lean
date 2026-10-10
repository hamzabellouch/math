import Mathlib
import OAI.Analysis.HardSphere.Conditioning.UnitPairCount

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

lemma unitOccupation_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    unitOccupation hL p v X≤n := by
  exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans (by simp))

lemma unitPairCount_le {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (X : Configuration n L) :
    unitPairCount hL p v X≤(n:ℝ)^2 := by
  have hn : 0≤(unitOccupation hL p v X:ℝ) := Nat.cast_nonneg _
  have hb : (unitOccupation hL p v X:ℝ)≤n := by exact_mod_cast unitOccupation_le hL p v X
  unfold unitPairCount
  nlinarith only [hn, mul_self_le_mul_self hn hb]

lemma unitPairCount_integrable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : Fin n → Prop) [DecidablePred p] (v : CubeCell K) (u : ScalarL2 n L) :
    Integrable (fun X ↦ unitPairCount hL p v X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (unitPairCount_measurable hL p v)
    (fun X ↦ by rw [abs_of_nonneg (unitPairCount_nonneg hL p v X)]; exact unitPairCount_le hL p v X)

lemma localizedNearLabels_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (s : ℝ) (u : ScalarL2 n L) :
    Integrable (fun X ↦ ((localizedNearLabels L A s X).card:ℝ)*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u ((measurable_of_countable (fun k : ℕ ↦ (k:ℝ))).comp (localizedNearLabels_card_measurable L A s))
    (B:=(n:ℝ)) (fun X ↦ by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show (localizedNearLabels L A s X).card≤n by simpa using (localizedNearLabels L A s X).card_le_univ))

def weightedUnitPairCount {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (X : Configuration n L) : ℝ :=
  ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*unitPairCount hL (fun _ ↦ True) v X

lemma weightedUnitPairCount_nonneg {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (X : Configuration n L) : 0≤weightedUnitPairCount hL A X :=
  Finset.sum_nonneg (fun v _ ↦ mul_nonneg (Real.exp_pos _).le (unitPairCount_nonneg hL _ v X))

lemma weightedUnitPairCount_integral {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (u : ScalarL2 n L) :
    (∫ X, weightedUnitPairCount hL A X*‖u X‖^2)=
      ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u X‖^2) := by
  simp only [weightedUnitPairCount,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro v _
    exact (unitPairCount_integrable hL _ v u).const_mul _

lemma weightedUnitPairCount_integrable {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedUnitPairCount hL A X*‖u X‖^2) volume := by
  simp only [weightedUnitPairCount,Finset.sum_mul,mul_assoc]
  exact integrable_finsetSum _ (fun v _ ↦ (unitPairCount_integrable hL _ v u).const_mul _)

lemma spatial_cell_average_real {n K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (A : Finset (Torus L)) {r : ℝ} (hr : 0<r) (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-1)/(64*Real.sqrt 3)*r*(∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  apply le_trans _ (spatial_cell_average hL A hr u hu)
  apply le_of_eq
  have hi (v : CubeCell K) : ENNReal.ofReal (∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2)=
      ∫⁻ X, ENNReal.ofReal (unitPairCount hL (fun _ ↦ True) v X)*ENNReal.ofReal (‖u.1 X‖^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (unitPairCount_integrable hL _ v u.1)
      (Eventually.of_forall (fun X ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _)))]
    simp only [ENNReal.ofReal_mul (unitPairCount_nonneg hL _ v _)]
  have hn (v : CubeCell K) : 0≤∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2 :=
    integral_nonneg (fun X ↦ mul_nonneg (unitPairCount_nonneg hL _ v X) (sq_nonneg _))
  rw [weightedUnitPairCount_integral,Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro v _
    have he : Real.exp (-1)/(64*Real.sqrt 3)*r*(Real.exp (-spatialSiteDistance L A (unitCenter L v))*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2))=
        Real.exp (-(spatialSiteDistance L A (unitCenter L v)+1))*(1/(64*Real.sqrt 3)*r)*(∫ X, unitPairCount hL (fun _ ↦ True) v X*‖u.1 X‖^2) := by
      rw [neg_add,Real.exp_add]
      ring
    rw [he,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (Real.exp_pos _).le,hi]
    exact mul_assoc _ _ _
  · intro v _
    exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_pos _).le (hn v))

lemma spatial_near_average_real {n : ℕ} (L : Length) (A : Finset (Torus L))
    {r s : ℝ} (hs : 0<s) (hs' : 2*s≤1) (hL : 10*s≤L.val) (hr : 0<r)
    (u : Jet n L) (hu : u∈dirichletDomain n L r) :
    ENNReal.ofReal (Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3*
      (∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2))≤
      ∫⁻ H, ENNReal.ofReal (spatialPartitionEnergy L A H u) ∂radiusLaw := by
  have hi : ENNReal.ofReal (∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)=
      ∫⁻ X, ((localizedNearLabels L A s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (localizedNearLabels_integrable L A s u.1)
      (Eventually.of_forall (fun X ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))]
    simp only [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul (by positivity),hi]
  exact spatial_near_average L A hs hs' hL hr u hu

theorem spatial_before_square : ∃ C D : ℝ, 0<C ∧ 0<D ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (r s : ℝ),
      0<r → 0<s → 2*s≤1 → 10*s≤L.val → (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
      Real.exp (-1)/(128*Real.sqrt 3)*r*(∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2)+
        Real.exp (-8)*(27/(524288*Real.sqrt 3))*r/s^3*(∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)-
        (C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2)≤energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,D,hC,hD,hsp⟩ := spatial_spectral_average
  refine ⟨C,D,hC,hD,?_⟩
  intro n K L hL r s hr hs hs' hsL hsmall g hg A hA u hu
  have hF : 0≤∫ X, weightedSiteCount L A X*‖u.1 X‖^2 :=
    integral_nonneg (fun X ↦ mul_nonneg (weightedSiteCount_nonneg L A X) (sq_nonneg _))
  have hLpos : 0<L.val := L.property
  have hB : 0≤energy u-energy g*‖u.1‖^2+(C*(n:ℝ)*r/L.val^3+D)*(∫ X, weightedSiteCount L A X*‖u.1 X‖^2) :=
    add_nonneg (sub_nonneg.mpr (hg.rayleigh_all u hu)) (mul_nonneg (by positivity) hF)
  have hc := (ENNReal.ofReal_le_ofReal_iff hB).mp ((spatial_cell_average_real hL A hr u hu).trans
    (hsp n L r hr hsmall g hg A hA u hu))
  have hk := (ENNReal.ofReal_le_ofReal_iff hB).mp ((spatial_near_average_real L A hs hs' hsL hr u hu).trans
    (hsp n L r hr hsmall g hg A hA u hu))
  have he : Real.exp (-1)/(128*Real.sqrt 3)*r=Real.exp (-1)/(64*Real.sqrt 3)*r/2 := by ring
  have he' : Real.exp (-8)*(27/(524288*Real.sqrt 3))*r/s^3=Real.exp (-8)*(27/(262144*Real.sqrt 3))*r/s^3/2 := by ring
  rw [he,he']
  linarith only [hc,hk]

end HardSphere

end

end OAI
