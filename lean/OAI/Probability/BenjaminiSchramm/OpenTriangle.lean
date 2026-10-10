import OAI.Probability.BenjaminiSchramm.DeletionLoss

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ennreal_distinctClusterMoment_fresh [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    ENNReal.ofReal (distinctClusterMoment G p x y) =
      ∫⁻ ω, ENNReal.ofReal (freshExteriorMoment G p x y ω) ∂law p := by
  change ENNReal.ofReal (∫ ω, (if ¬Conn G ω x y then
    ((cluster G ω x).ncard : ℝ) * ((cluster G ω y).ncard : ℝ) else 0) ∂law p) = _
  rw [←integral_freshExteriorMoment G hloc hqt p hp x y]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_freshExteriorMoment G hloc hqt p hp x y)
    (Filter.Eventually.of_forall (freshExteriorMoment_nonneg G p x y))

theorem freshExteriorMoment_deletion_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x y : V)
    (ω : Set E) (hfin : (cluster G ω x).Finite) :
    ENNReal.ofReal (susceptibility G p y) * clusterMass G ω x ≤
      ENNReal.ofReal (freshExteriorMoment G p x y ω) + C * clusterDeletionLoss G p x y ω := by
  have hd := susceptibility_deletion_ennreal G hloc hqt p hp (cluster G ω x)ᶜ C hC y
  have hd' : ENNReal.ofReal (susceptibility G p y) ≤
      ENNReal.ofReal (inducedSusceptibility G (cluster G ω x)ᶜ p y) +
        (∑' z, if Conn G ω x z then law p {η | Conn G η y z} else 0) * C := by
    simpa only [Set.mem_compl_iff,cluster,Set.mem_ofPred_eq,ite_not] using hd
  have hm := mul_le_mul' hd' (le_refl (clusterMass G ω x))
  rw [add_mul] at hm
  have hf : ENNReal.ofReal (freshExteriorMoment G p x y ω) =
      ENNReal.ofReal (inducedSusceptibility G (cluster G ω x)ᶜ p y) * clusterMass G ω x := by
    rw [freshExteriorMoment,ENNReal.ofReal_mul (Nat.cast_nonneg _),
      clusterMass_eq_ncard G ω x hfin]
    simp only [ENNReal.ofReal_natCast,mul_comm]
  rw [hf]
  dsimp only [clusterDeletionLoss]
  convert hm using 1
  ring

theorem distinctClusterMoment_openTriangle [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (C : ℝ≥0∞)
    (hC : ∀ z, ENNReal.ofReal (susceptibility G p z) ≤ C) (x y : V) :
    ENNReal.ofReal (susceptibility G p x) * ENNReal.ofReal (susceptibility G p y) ≤
      ENNReal.ofReal (distinctClusterMoment G p x y) + C ^ 2 * openTriangle G p x y := by
  have hpoint : (fun ω => ENNReal.ofReal (susceptibility G p y) * clusterMass G ω x) ≤ᵐ[law p]
      (fun ω => ENNReal.ofReal (freshExteriorMoment G p x y ω) + C * clusterDeletionLoss G p x y ω) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    exact freshExteriorMoment_deletion_bound G hloc hqt p hp C hC x y ω hω
  have h := lintegral_mono_ae hpoint
  rw [lintegral_const_mul _ (measurable_clusterMass G x),lintegral_clusterMass,
    ←ennreal_susceptibility G hloc hqt p hp x] at h
  rw [lintegral_add_left (Measurable.ennreal_ofReal (measurable_freshExteriorMoment G p x y)),
    ←ennreal_distinctClusterMoment_fresh G hloc hqt p hp x y,
    lintegral_const_mul _ (measurable_clusterDeletionLoss G p x y)] at h
  have hrow (z : V) : (∑' u, law p {ω | Conn G ω z u}) ≤ C := by
    rw [←ennreal_susceptibility G hloc hqt p hp z]
    exact hC z
  have hb := mul_le_mul' (le_refl C) (clusterDeletionLoss_openTriangle_bound G p C hrow x y)
  have he : C * (C * openTriangle G p x y) = C ^ 2 * openTriangle G p x y := by ring
  rw [he] at hb
  have h' : ENNReal.ofReal (susceptibility G p x) * ENNReal.ofReal (susceptibility G p y) ≤
      ENNReal.ofReal (distinctClusterMoment G p x y) +
        C * ∫⁻ ω, clusterDeletionLoss G p x y ω ∂law p := by
    simpa only [mul_comm] using h
  exact h'.trans (add_le_add_right hb _)

end Percolation.BenjaminiSchramm

end OAI
