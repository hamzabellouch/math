import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDegree

namespace OAI

/-! The actual Iwahori(p^3) fundamental domain underlying the cubed-prime
trace. It consists of precisely the finite cosets enumerated above. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeCubeCoverDomain (p : Eisenstein) : Set CubicThetaPoint :=
  ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain

lemma cubicThetaPrimeCubeCoverDomain_measurable {p : Eisenstein} (hp : primaryPrime p) :
    MeasurableSet (cubicThetaPrimeCubeCoverDomain p) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  apply MeasurableSet.iUnion
  intro t
  exact (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
    cubicThetaFundamentalDomain_measurable

theorem cubicThetaPrimeCubeCoverDomain_unique (p : Eisenstein) (x : CubicThetaPoint) :
    ∃! g : cubicThetaPrimeIwahori (p^3),g • x∈cubicThetaPrimeCubeCoverDomain p := by
  obtain ⟨a,ha,hua⟩ := cubicThetaFundamentalDomain_unique x
  obtain ⟨⟨h,t⟩,he,hunique⟩ := (cubicThetaPrimeCubeTransversal_complement p).existsUnique a⁻¹
  have hmove : h.val⁻¹=t.val*a := by
    calc
      _ = h.val⁻¹*(a⁻¹*a) := by simp
      _ = h.val⁻¹*((h.val*t.val)*a) := by rw [he]
      _ = _ := by group
  refine ⟨h⁻¹,?_,?_⟩
  · apply mem_iUnion.mpr
    refine ⟨t,a • x,ha,?_⟩
    change t.val • (a • x)=h.val⁻¹ • x
    rw [←mul_smul,hmove]
  · intro k hk
    obtain ⟨u,hu⟩ := mem_iUnion.mp hk
    obtain ⟨y,hy,hky⟩ := hu
    have hya : u.val⁻¹*k.val=a := by
      apply hua
      rw [mul_smul]
      change u.val⁻¹ • (k • x)∈cubicThetaFundamentalDomain
      rw [←hky,inv_smul_smul]
      exact hy
    have hpair : ((k⁻¹,u) : cubicThetaPrimeIwahori (p^3) × cubicThetaPrimeCubeTransversal p)=(h,t) := by
      apply hunique
      change k.val⁻¹*u.val=a⁻¹
      rw [←hya]
      group
    have hh : k⁻¹=h := congrArg Prod.fst hpair
    simpa only [inv_inv] using congrArg Inv.inv hh

theorem cubicThetaPrimeCubeCoverDomain_isFundamentalDomain {p : Eisenstein}
    (hp : primaryPrime p) (μ : Measure CubicThetaPoint) :
    IsFundamentalDomain (cubicThetaPrimeIwahori (p^3)) (cubicThetaPrimeCubeCoverDomain p) μ :=
  IsFundamentalDomain.mk' (cubicThetaPrimeCubeCoverDomain_measurable hp).nullMeasurableSet
    (cubicThetaPrimeCubeCoverDomain_unique p)

lemma cubicThetaPrimeCubeCoverDomain_disjoint (p : Eisenstein) :
    Pairwise (fun t u : cubicThetaPrimeCubeTransversal p =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
  intro t u htu
  exact cubicThetaFundamentalDomain_translates_disjoint (fun he => htu (Subtype.ext he))

end CubicFirstMoment

end

end OAI
