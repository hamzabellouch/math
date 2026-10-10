import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFiniteEnergy

namespace OAI

/-! Linearity of the literal cubed-prime Hecke correspondence, including
its action on actual finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeHecke_add {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    cubicThetaPrimeCubeHecke hp (F+G)=cubicThetaPrimeCubeHecke hp F+cubicThetaPrimeCubeHecke hp G := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    (F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))+
      G.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))))=_
  change _ = (cubicThetaPrimeCubeHecke hp F).val x +
    (cubicThetaPrimeCubeHecke hp G).val x
  rw [cubicThetaPrimeCubeHecke_apply, cubicThetaPrimeCubeHecke_apply]
  simp only [tsum_fintype,mul_add,Finset.sum_add_distrib]

lemma cubicThetaPrimeCubeHecke_smul {p : Eisenstein} (hp : primaryPrime p)
    (c : ℂ) (F : CubicThetaSection) :
    cubicThetaPrimeCubeHecke hp (c • F)=c • cubicThetaPrimeCubeHecke hp F := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
    (c*F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))))=
      c*∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x))
  simp only [tsum_fintype,mul_left_comm,Finset.mul_sum]

def cubicThetaPrimeCubeHeckeLinear {p : Eisenstein} (hp : primaryPrime p) :
    CubicThetaSection →ₗ[ℂ] CubicThetaSection where
  toFun := cubicThetaPrimeCubeHecke hp
  map_add' := cubicThetaPrimeCubeHecke_add hp
  map_smul' := cubicThetaPrimeCubeHecke_smul hp

def cubicThetaPrimeCubeHeckeFiniteLinear {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaFiniteEnergySections where
  toFun := cubicThetaPrimeCubeHeckeFinite hp
  map_add' F G := by
    apply Subtype.ext
    exact cubicThetaPrimeCubeHecke_add hp F.val G.val
  map_smul' c F := by
    apply Subtype.ext
    exact cubicThetaPrimeCubeHecke_smul hp c F.val

end CubicFirstMoment

end

end OAI
