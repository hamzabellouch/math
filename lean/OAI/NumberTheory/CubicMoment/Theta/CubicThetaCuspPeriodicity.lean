import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedCoefficient

namespace OAI

/-! The three actual cusp coefficient families depend only on the integer
cusp index modulo three. This is inherited from their literal support. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspIndex_congr {x y : Eisenstein} (h : (3:Eisenstein)∣x-y) :
    (3:ℤ)∣cubicThetaCuspIndex x-cubicThetaCuspIndex y := by
  obtain ⟨t,ht⟩ := h
  refine ⟨cubicThetaCuspIndex t,?_⟩
  have he : x-y=(3:ℤ) • t := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using ht
  have hh := congrArg (fun z : Eisenstein => coordinatesEquiv.symm z 1) he
  simpa only [cubicThetaCuspIndex,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul] using hh

lemma cubicThetaCuspIndex_omega (j : ℤ) :
    cubicThetaCuspIndex ((j:Eisenstein)*omegaE)=j := by
  have he : coordinatesEquiv ![(0:ℤ),j]=(j:Eisenstein)*omegaE := by
    change ofCoords 0 j=_
    simp [ofCoords]
  unfold cubicThetaCuspIndex
  rw [←he,LinearEquiv.symm_apply_apply]
  rfl

lemma cubicThetaActualCuspCoefficient_periodic {m n : ℤ} (h : (3:ℤ)∣n-m) :
    cubicThetaActualCuspCoefficient n=cubicThetaActualCuspCoefficient m := by
  have he : (3:ℤ)∣n ↔ (3:ℤ)∣m := by
    constructor
    · intro hn
      have hm := dvd_sub hn h
      simpa only [sub_sub_cancel] using hm
    · intro hm
      have hn := dvd_add h hm
      simpa only [sub_add_cancel] using hn
  by_cases hn : (3:ℤ)∣n
  · simp only [cubicThetaActualCuspCoefficient,hn,he.mp hn,ite_true]
  · have hm := mt he.mpr hn
    simp only [cubicThetaActualCuspCoefficient,hn,hm,ite_false]
    funext k
    unfold cubicThetaShiftedLatticeCoefficient
    have hnm : lambdaE∣(n:Eisenstein)-(m:Eisenstein) := by
      obtain ⟨t,ht⟩ := h
      have hl : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by
        rw [mul_neg,←pow_two,lambdaE_sq,neg_neg]⟩
      apply dvd_trans hl
      exact ⟨(t:Eisenstein),by exact_mod_cast ht⟩
    have hiff : lambdaE∣k-(n:Eisenstein) ↔ lambdaE∣k-(m:Eisenstein) := by
      constructor
      · intro hk
        convert dvd_add hk hnm using 1
        ring
      · intro hk
        convert dvd_sub hk hnm using 1
        ring
    rw [hiff]

lemma cubicThetaProjectedCuspType_congr (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (ha : (3:Eisenstein)∣g 0 0) (j : Fin 3) :
    (3:ℤ)∣cubicThetaProjectedCuspType g j-(j.val:ℤ) := by
  have hj : cubicThetaProjectedCuspMatrix g j 0 0=
      g 0 0+(j.val:Eisenstein)*omegaE*g 1 0 := by
    change ((!![1,(j.val:Eisenstein)*omegaE;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 0 0=_
    simp [Matrix.mul_apply,Fin.sum_univ_two]
  have h : (3:Eisenstein)∣cubicThetaProjectedCuspMatrix g j 0 0-(j.val:Eisenstein)*omegaE := by
    rw [hj]
    convert dvd_add ha (dvd_mul_of_dvd_right hc ((j.val:Eisenstein)*omegaE)) using 1
    ring
  have hh := cubicThetaCuspIndex_congr h
  have hjindex : cubicThetaCuspIndex ((j.val:Eisenstein)*omegaE)=(j.val:ℤ) := by
    simpa only [Int.cast_natCast] using cubicThetaCuspIndex_omega (j.val:ℤ)
  rw [hjindex] at hh
  exact hh

end CubicFirstMoment

end

end OAI
