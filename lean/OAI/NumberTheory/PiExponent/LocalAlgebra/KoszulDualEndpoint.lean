import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

theorem dualCone_endpoint_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgh : g.dualMap.comp h.dualMap = 0)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      have hz : g.dualMap (h.dualMap β) = 0 := LinearMap.congr_fun hgh β
      simp only [map_sub, map_smul, hz, sub_zero, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end PiExponentSiegelAux.W30

end OAI
