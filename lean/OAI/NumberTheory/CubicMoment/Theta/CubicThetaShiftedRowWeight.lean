import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedCuspPeriodicity

namespace OAI

/-! Zero-extended periodic weights of the translated inverted rows.
The finite residue modulus is `3*c` in the variable `d=3*u`. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicTheta_coprime_add_left (c d b : Eisenstein) :
    IsCoprime (c+b*d) d ↔ IsCoprime c d := by
  constructor
  · rintro ⟨u,v,h⟩
    refine ⟨u,u*b+v,?_⟩
    linear_combination h
  · rintro ⟨u,v,h⟩
    refine ⟨u,v-u*b,?_⟩
    linear_combination h

lemma cubicTheta_coprime_add_right (c d b : Eisenstein) :
    IsCoprime c (d+b*c) ↔ IsCoprime c d := by
  rw [isCoprime_comm,cubicTheta_coprime_add_left,isCoprime_comm]

def cubicThetaShiftedRowWeight (b c u : Eisenstein) : ℂ :=
  cubicSymbol (c+b*(3*u)) (3*u)

lemma cubicThetaShiftedRowWeight_norm {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) : ‖cubicThetaShiftedRowWeight b c u‖ ≤ 1 :=
  norm_cubicSymbol_le_one (cubicTheta_primary_add_three_mul hc ⟨u,rfl⟩ b) _

lemma cubicThetaShiftedRowWeight_periodic {c : Eisenstein} (hc : primary c)
    (b u m : Eisenstein) :
    cubicThetaShiftedRowWeight b c (u+(3*c)*m)=cubicThetaShiftedRowWeight b c u := by
  have hd : 3*(u+(3*c)*m)=3*u+9*m*c := by ring
  by_cases hcop : IsCoprime c (3*u)
  · let r : CubicThetaInvertedRow := ⟨c,3*u,hc,⟨u,rfl⟩,hcop⟩
    have he := cubicThetaShiftedRowPhase_periodic b m r
    simpa only [cubicThetaShiftedRowPhase,cubicThetaShiftedRowTranslate,r,
      cubicThetaShiftedRowWeight,hd] using he
  · have hcop' : ¬IsCoprime c (3*(u+(3*c)*m)) := by
      rw [hd,cubicTheta_coprime_add_right]
      exact hcop
    have hz (v : Eisenstein) (hv : ¬IsCoprime c (3*v)) : cubicThetaShiftedRowWeight b c v=0 := by
      apply cubicSymbol_eq_zero_of_not_isCoprime
        (cubicTheta_primary_add_three_mul hc ⟨v,rfl⟩ b)
      rwa [cubicTheta_coprime_add_left]
    rw [hz _ hcop',hz _ hcop]

lemma cubicThetaShiftedRowWeight_congr {c u v : Eisenstein} (hc : primary c)
    (b : Eisenstein) (h : (3*c)∣u-v) :
    cubicThetaShiftedRowWeight b c u=cubicThetaShiftedRowWeight b c v := by
  obtain ⟨m,hm⟩ := h
  have he : u=v+(3*c)*m := by linear_combination hm
  rw [he,cubicThetaShiftedRowWeight_periodic hc]

def cubicThetaShiftedResidueWeight (b c : Eisenstein) (x : Residues (3*c)) : ℂ :=
  cubicThetaShiftedRowWeight b c (residueRepresentative (3*c) x)

lemma cubicThetaShiftedResidueWeight_mk {c : Eisenstein} (hc : primary c)
    (b u : Eisenstein) :
    cubicThetaShiftedResidueWeight b c (Ideal.Quotient.mk (modulus (3*c)) u)=
      cubicThetaShiftedRowWeight b c u := by
  apply cubicThetaShiftedRowWeight_congr hc b
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus (3*c))
    (residueRepresentative (3*c) (Ideal.Quotient.mk (modulus (3*c)) u)-u)=0
  rw [map_sub,residueRepresentative_spec,sub_self]

def cubicThetaShiftedGaussCoefficient (b c h : Eisenstein) : ℂ :=
  ∑' x : Residues (3*c), cubicThetaShiftedResidueWeight b c x*
    (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
      ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))):ℂ)

lemma cubicThetaShiftedGaussCoefficient_norm {c : Eisenstein} (hc : primary c)
    (b h : Eisenstein) :
    ‖cubicThetaShiftedGaussCoefficient b c h‖ ≤ (Nat.card (Residues (3*c)):ℝ) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) (primary_ne_zero hc))
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  unfold cubicThetaShiftedGaussCoefficient
  rw [tsum_fintype,Nat.card_eq_fintype_card]
  calc
    _ ≤ ∑ x : Residues (3*c), ‖cubicThetaShiftedResidueWeight b c x*
        (Real.fourierChar (tracePair (residueRepresentative (3*c) x:ℂ)
          ((h:ℂ)/(((3*c:Eisenstein):ℂ)*traceLambda))):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residues (3*c), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul,Circle.norm_coe,mul_one]
      exact cubicThetaShiftedRowWeight_norm hc b _
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
