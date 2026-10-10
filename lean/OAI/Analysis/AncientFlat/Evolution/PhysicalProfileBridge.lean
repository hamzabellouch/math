import OAI.Analysis.AncientFlat.Evolution.FinitePhysicalAncient
import OAI.Analysis.AncientFlat.Profile.ProfileSymbols
import OAI.Analysis.AncientFlat.Weighted.WeightedSource
import OAI.Analysis.AncientFlat.Weighted.ExactXNorm
import OAI.Analysis.AncientFlat.Weighted.WeightedEstimate

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParabolicAnnular FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma exp_similarity (t k : ℝ) (ht : t<0) :
    Real.exp (k*similarityTime t)=(-t)^(-k) := by
  rw [Real.rpow_def_of_pos (neg_pos.mpr ht)]
  congr 1
  dsimp [similarityTime]
  ring
lemma similarity_exp (t : ℝ) (ht : t<0) : Real.exp (similarityTime t)=(-t)⁻¹ := by
  simpa only [one_mul,neg_one_mul,Real.rpow_neg_one] using exp_similarity t 1 ht
lemma similarity_radius (t : ℝ) (ht : t<0) (x : V) :
    ‖Real.exp (similarityTime t/4) • x‖^2=‖x‖^2/Real.sqrt (-t) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow,←Real.exp_nat_mul]
  have he : Real.exp ((2:ℕ)* (similarityTime t/4))= (Real.sqrt (-t))⁻¹ := by
    rw [show (2:ℕ)*(similarityTime t/4)=(1/2:ℝ)*similarityTime t by push_cast; ring,
      exp_similarity t (1/2) ht,Real.sqrt_eq_rpow,Real.rpow_neg (neg_pos.mpr ht).le]
  rw [he]
  ring
lemma profile_physical_principal (G : ℝ → ℝ) {t : ℝ} (ht : t<0) (x : V) :
    physicalPrincipal (profileAf G) t x=profilePrincipal G (x,t) := by
  simp only [physicalPrincipal,profileAf,profilePrincipal,similarity_radius t ht x]
lemma profile_physical_potential (G : ℝ → ℝ) {t : ℝ} (ht : t<0) (x : V) :
    physicalPotential (profileBf G) t x=profilePotential G (x,t) := by
  simp only [physicalPotential,profileBf,profilePotential,similarity_radius t ht x,similarity_exp t ht]
  ring
lemma force_source_identity (γ : ℝ) (f : V × ℝ → ℂ) (j : ℝ →ᵇ C₀(V,ℂ))
    (hj : ∀ τ z, j τ z=FlatWeighted.normalizedSource γ f τ z)
    {t : ℝ} (ht : t<0) (x : V) : physicalForce γ j t x=f (x,t) := by
  rw [physicalForce,physical_apply,hj]
  unfold FlatWeighted.normalizedSource
  have he : -Real.exp (-similarityTime t)=t := by
    simp only [similarityTime,neg_neg,Real.exp_log (neg_pos.mpr ht)]
  have hx : Real.exp (-similarityTime t/4) • Real.exp (similarityTime t/4) • x=x := by
    rw [smul_smul,←Real.exp_add,show -similarityTime t/4+similarityTime t/4=0 by ring,Real.exp_zero,one_smul]
  rw [he,hx]
  simp only [Complex.real_smul,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add]
  have he2 : (1/2-(γ-1))*similarityTime t+(γ-3/2)*similarityTime t=0 := by ring
  rw [he2,Real.exp_zero,Complex.ofReal_one,one_mul]
lemma profile_radial (G : ℝ → ℝ) :
    Radial (profileAf (V := V) G) ∧ Radial (profileBf (V := V) G) := by
  constructor <;> intro R x <;> simp [profileAf,profileBf,R.norm_map]
end FlatSimilarity

end

end OAI
