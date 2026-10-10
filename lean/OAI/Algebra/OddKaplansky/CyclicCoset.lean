import OAI.Algebra.OddKaplansky.NilpotentBasis

namespace OAI

universe contextUniverse1

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4

section
namespace OddKaplansky.CosetMatrix
noncomputable section
open scoped Classical BigOperators
open CosetCoordinates
variable {K : Type portUniverse1} {G : Type portUniverse2} [Field K] [Group G] [sectionInstance70 : Fintype G] (T : Subgroup G)
lemma mk_right
    {G : Type contextUniverse1}
    [contextInstance1 : Group.{contextUniverse1} G]
    [Fintype.{contextUniverse1} G]
    (T : @Subgroup.{contextUniverse1} G contextInstance1) (g : G) (t : T) : ((g*t : G) : G ⧸ T) = (g : G ⧸ T) :=
  QuotientGroup.mk_mul_of_mem _ t.property
lemma residue_right (g : G) (t : T) : residue T (g*t) = residue T g * t := by
  apply Subtype.ext
  simp only [residue,mk_right,Subgroup.coe_mul,mul_assoc]
lemma unpack_right_single (v : (G ⧸ T) → D (K := K) T) (t : T) :
    unpack T (fun q => v q * MonoidAlgebra.single t 1) =
      unpack T v * MonoidAlgebra.single (t : G) 1 := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [unpack_coeff,MonoidAlgebra.coeff_mul_single_apply,MonoidAlgebra.coeff_mul_single_apply,
    unpack_coeff,mul_one,mul_one]
  simp only [← Subgroup.coe_inv,mk_right,residue_right]
lemma unpack_right (v : (G ⧸ T) → D (K := K) T) (b : D (K := K) T) :
    unpack T (fun q => v q * b) = unpack T v * MonoidAlgebra.mapDomainAlgHom K K T.subtype b := by
  induction b using MonoidAlgebra.induction_on with
  | of t =>
    convert unpack_right_single T v t using 1 <;> simp [MonoidAlgebra.of_apply]
  | add b c hb hc =>
    simp only [mul_add,map_add]
    change unpack T ((fun q => v q*b)+(fun q => v q*c)) = _
    rw [map_add,hb,hc]
  | smul c b hb =>
    simp only [mul_smul_comm,map_smul]
    change unpack T (c • (fun q => v q*b)) = _
    rw [map_smul,hb]
lemma right_divisible (X : D (K := K) T) (n k : ℕ)
    (hdiv : ∀ a : D (K := K) T, a*X^n=0 → ∃ b, a=b*X^k)
    (a : MonoidAlgebra K G) (ha : a*(MonoidAlgebra.mapDomainAlgHom K K T.subtype X)^n=0) :
    ∃ b, a=b*(MonoidAlgebra.mapDomainAlgHom K K T.subtype X)^k := by
  let v := (unpack (K := K) T).symm a
  have hv : ∀ q, v q * X^n=0 := by
    have hh : unpack T (fun q => v q*X^n)=0 := by
      rw [unpack_right,map_pow,LinearEquiv.apply_symm_apply,ha]
    have hz := (unpack T).injective (hh.trans (map_zero (unpack T)).symm)
    exact fun q => congrFun hz q
  choose w hw using fun q => hdiv (v q) (hv q)
  refine ⟨unpack T w,?_⟩
  rw [← map_pow,← unpack_right]
  exact (LinearEquiv.apply_symm_apply (unpack T) a).symm.trans (congrArg (unpack T) (funext hw))
end
end OddKaplansky.CosetMatrix

namespace OddKaplansky.CyclicAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse3} {G : Type portUniverse4} [Field K] [Group G] [Fintype G]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
lemma embedded_right_divisible (i : C p →* G) (hi : Function.Injective i)
    (ell : ℕ) (hell : ell≤p) (a : MonoidAlgebra K G)
    (ha : a*(MonoidAlgebra.single (i (gen p)) 1-1)^ell=0) :
    ∃ b, a=b*(MonoidAlgebra.single (i (gen p)) 1-1)^(p-ell) := by
  let φ := MonoidAlgebra.domCongr K K (MonoidHom.ofInjective hi)
  let Xi := φ (X (K := K) p)
  have hXi : MonoidAlgebra.mapDomainAlgHom K K i.range.subtype Xi =
      MonoidAlgebra.single (i (gen p)) (1 : K)-1 := by
    simp only [Xi,φ,X,map_sub,map_one,MonoidAlgebra.domCongr_single]
    simp only [MonoidAlgebra.mapDomainAlgHom_apply,MonoidAlgebra.mapDomain_single]
    rfl
  apply CosetMatrix.right_divisible i.range Xi ell (p-ell) _ a (by rwa [hXi]) |>.imp (fun b hb => by rwa [hXi] at hb)
  intro c hc
  have hcz : φ.symm c * X p^ell=0 := by
    apply φ.injective
    simpa only [map_mul,map_pow,AlgEquiv.apply_symm_apply,map_zero] using hc
  obtain ⟨b,hb⟩ := right_divisible p ell hell (φ.symm c) hcz
  refine ⟨φ b,?_⟩
  have hh := congrArg φ hb
  simpa only [map_mul,map_pow,AlgEquiv.apply_symm_apply] using hh
end
end OddKaplansky.CyclicAlgebra

end

end OAI
