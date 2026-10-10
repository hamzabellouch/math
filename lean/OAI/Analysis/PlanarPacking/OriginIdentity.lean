import OAI.Analysis.PlanarPacking.ExactJets
import OAI.Analysis.PlanarPacking.LatticePoisson

namespace OAI

/-! # Equality at the origin from triangular lattice contacts and Poisson summation -/

namespace SharpPlanar
noncomputable def exactLeft : SchwartzMap Plane ℝ := pairLeft exactData₁ exactData₂
noncomputable def exactRight : SchwartzMap Plane ℝ := pairRight exactData₁ exactData₂
lemma exactLeft_apply (x : Plane) : exactLeft x=Real.exp (-Real.pi*h*(b*‖x‖^2))*H₁ (b*‖x‖^2) :=
  pairLeft_apply _ _ _
lemma exactRight_apply (x : Plane) : exactRight x=Real.exp (-Real.pi*h*(b*‖x‖^2))*H₂ (b*‖x‖^2) :=
  pairRight_apply _ _ _
lemma nonzero_swap {p : ℤ×ℤ} (hp : p≠0) : (p.2,p.1)≠0 := by
  intro hh
  apply hp
  exact Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh)
lemma exactLeft_lattice_zero {p : ℤ×ℤ} (hp : p≠0) : exactLeft (latticePoint p)=0 := by
  rw [exactLeft_apply]
  change Real.exp _*H₁ (b*‖hexPoint (p.2,p.1)‖^2)=_
  rw [hexPoint_radius]
  have hh: H₁ (hexNat (p.2,p.1):ℝ)=0 := (H₁_jets (hexNode (p.2,p.1) (nonzero_swap hp))).1
  rw [hh,mul_zero]
lemma exactRight_lattice_zero {p : ℤ×ℤ} (hp : p≠0) : exactRight (latticePoint p)=0 := by
  rw [exactRight_apply]
  change Real.exp _*H₂ (b*‖hexPoint (p.2,p.1)‖^2)=_
  rw [hexPoint_radius]
  have hh: H₂ (hexNat (p.2,p.1):ℝ)=0 := (H₂_jets (hexNode (p.2,p.1) (nonzero_swap hp))).1
  rw [hh,mul_zero]
lemma exact_origin_identity : exactLeft 0=exactRight 0 := by
  have hh:=pair_lattice_poisson exactData₁ exactData₂
  change (∑' p : ℤ×ℤ, exactLeft (latticePoint p))=(∑' p : ℤ×ℤ, exactRight (latticePoint p)) at hh
  rw [tsum_eq_single (0 : ℤ×ℤ) (fun p hp => exactLeft_lattice_zero hp),
    tsum_eq_single (0 : ℤ×ℤ) (fun p hp => exactRight_lattice_zero hp),latticePoint_zero] at hh
  exact hh
end SharpPlanar

end OAI
