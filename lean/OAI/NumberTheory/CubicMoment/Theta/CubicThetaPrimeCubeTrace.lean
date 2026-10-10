import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTransversal

namespace OAI

/-! The literal finite cubed-prime trace, with its cubic multipliers.
Composing it with dilation gives the actual cubed-prime Hecke operator. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeTraceTerm (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) : ℂ :=
  star (cubicThetaKubotaValue g)*F.val (g • x)

lemma cubicThetaPrimeCubeTraceTerm_left (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (h : cubicThetaPrimeIwahori (p^3)) (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (h.val*g) x=cubicThetaPrimeCubeTraceTerm p F g x := by
  have hu : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  unfold cubicThetaPrimeCubeTraceTerm
  rw [mul_smul,F.property,cubicThetaKubotaValue_mul,star_mul]
  calc
    _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*
      (star (cubicThetaKubotaValue g)*F.val (g • x)) := by ring
    _ = _ := by rw [hu,one_mul]

lemma cubicThetaPrimeCubeTraceTerm_translate (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g h : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F g (h • x)=
      cubicThetaKubotaValue h*cubicThetaPrimeCubeTraceTerm p F (g*h) x := by
  have hu : cubicThetaKubotaValue h*star (cubicThetaKubotaValue h)=1 := by
    rw [Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (cubicThetaKubotaValue h*star (cubicThetaKubotaValue h))*
      cubicThetaPrimeCubeTraceTerm p F g (h • x) := by rw [hu,one_mul]
    _ = _ := by
      simp only [cubicThetaPrimeCubeTraceTerm,cubicThetaKubotaValue_mul,star_mul,mul_smul]
      ring

lemma cubicThetaPrimeCubeTraceTerm_permute (p : Eisenstein) (F : cubicThetaPrimeCubeSections p)
    (g : cubicThetaPrincipalGroup) (t : cubicThetaPrimeCubeTransversal p) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeTraceTerm p F (t.val*g) x=
      cubicThetaPrimeCubeTraceTerm p F (cubicThetaPrimeCubeCosetPermutation p g t).val x := by
  rw [←cubicThetaPrimeCubeCosetPermutation_factor p g t,cubicThetaPrimeCubeTraceTerm_left]

def cubicThetaPrimeCubeTraceSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : CubicThetaSection := by
  letI : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  letI := Fintype.ofFinite (cubicThetaPrimeCubeTransversal p)
  refine ⟨⟨fun x => ∑' t : cubicThetaPrimeCubeTransversal p,
    cubicThetaPrimeCubeTraceTerm p F t.val x,?_⟩,?_⟩
  · simp only [tsum_fintype]
    apply continuous_finsetSum
    intro t _
    exact continuous_const.mul (F.val.continuous.comp (continuous_const_smul t.val))
  · intro g x
    change (∑' t : cubicThetaPrimeCubeTransversal p, cubicThetaPrimeCubeTraceTerm p F t.val (g • x))=
      cubicThetaKubotaValue g*(∑' t : cubicThetaPrimeCubeTransversal p,
        cubicThetaPrimeCubeTraceTerm p F t.val x)
    simp only [tsum_fintype]
    simp_rw [cubicThetaPrimeCubeTraceTerm_translate,cubicThetaPrimeCubeTraceTerm_permute]
    rw [←Finset.mul_sum]
    exact congrArg (fun a : ℂ => cubicThetaKubotaValue g*a)
      (Equiv.sum_comp (cubicThetaPrimeCubeCosetPermutation p g)
        (fun t => cubicThetaPrimeCubeTraceTerm p F t.val x))

def cubicThetaPrimeCubeHecke {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : CubicThetaSection :=
  cubicThetaPrimeCubeTraceSection hp (cubicThetaPrimeCubeDilationSection hp F)

lemma cubicThetaPrimeCubeHecke_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeCubeHecke hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p, star (cubicThetaKubotaValue t.val)*
        F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • (t.val • x)) := rfl

end CubicFirstMoment

end

end OAI
