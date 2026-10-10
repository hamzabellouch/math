import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramRowPeriodicity

namespace OAI

/-! The finite arithmetic weight exposed by the actual off-diagonal
Gram integrals. It keeps the primary and coprimality zero extension. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaKloostermanWeight (h k c : Eisenstein) (hc : (3:Eisenstein)∣c)
    (d : Eisenstein) : ℂ :=
  if hd : primary d ∧ IsCoprime c d then
    cubicThetaGramRowPhase h k ⟨c,d,hc,hd.1,hd.2⟩ else 0

lemma cubicThetaKloosterman_admissible_shift (c d m : Eisenstein) :
    (primary (d+3*c*m) ∧ IsCoprime c (d+3*c*m)) ↔ (primary d ∧ IsCoprime c d) := by
  have hp : primary (d+3*c*m) ↔ primary d := by
    have h3 : (3:Eisenstein)∣3*c*m := ⟨c*m,by ring⟩
    change (3:Eisenstein)∣(d+3*c*m)-1 ↔ (3:Eisenstein)∣d-1
    rw [show (d+3*c*m)-1=(d-1)+3*c*m by ring]
    simpa only [add_comm] using (dvd_add_right h3 :
      (3:Eisenstein)∣3*c*m+(d-1) ↔ (3:Eisenstein)∣d-1)
  have hg : IsCoprime c (d+3*c*m) ↔ IsCoprime c d := by
    rw [show d+3*c*m=d+c*(3*m) by ring]
    exact IsCoprime.add_mul_left_right_iff
  exact and_congr hp hg

theorem cubicThetaKloostermanWeight_periodic (h k : Eisenstein)
    {c : Eisenstein} (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (d m : Eisenstein) :
    cubicThetaKloostermanWeight h k c hc (d+3*c*m)=cubicThetaKloostermanWeight h k c hc d := by
  classical
  by_cases hd : primary d ∧ IsCoprime c d
  · have hdm := (cubicThetaKloosterman_admissible_shift c d m).mpr hd
    rw [cubicThetaKloostermanWeight,dite_eq_left hdm,cubicThetaKloostermanWeight,dite_eq_left hd]
    let r : CubicThetaBottomRow := ⟨c,d,hc,hd.1,hd.2⟩
    have he : (⟨c,d+3*c*m,hc,hdm.1,hdm.2⟩:CubicThetaBottomRow)=
        r.rightMul (cubicThetaPrincipalTranslation m) := by
      apply CubicThetaBottomRow.ext
      · exact (cubicThetaRow_right_translation_c r m).symm
      · exact (cubicThetaRow_right_translation_d r m).symm
    rw [he]
    exact cubicThetaGramRowPhase_translation h k r hc0 m
  · have hdm : ¬(primary (d+3*c*m) ∧ IsCoprime c (d+3*c*m)) :=
      fun hx => hd ((cubicThetaKloosterman_admissible_shift c d m).mp hx)
    rw [cubicThetaKloostermanWeight,dite_eq_right hdm,cubicThetaKloostermanWeight,dite_eq_right hd]

lemma cubicThetaGramRowPhase_norm (h k : Eisenstein) (r : CubicThetaBottomRow) :
    ‖cubicThetaGramRowPhase h k r‖=1 := by
  have hn (a : Eisenstein) (z : ℂ) : ‖cubicThetaHorizontalCharacter a z‖=1 := by
    unfold cubicThetaHorizontalCharacter
    exact Circle.norm_coe _
  simp only [cubicThetaGramRowPhase,norm_mul,norm_star,r.phase_norm,hn,mul_one]

lemma cubicThetaKloostermanWeight_norm (h k c : Eisenstein) (hc : (3:Eisenstein)∣c)
    (d : Eisenstein) : ‖cubicThetaKloostermanWeight h k c hc d‖≤1 := by
  classical
  unfold cubicThetaKloostermanWeight
  split_ifs
  · exact (cubicThetaGramRowPhase_norm _ _ _).le
  · simp

def cubicThetaKloostermanSum (h k c : Eisenstein) (hc : (3:Eisenstein)∣c) : ℂ :=
  ∑' x : Residues (3*c),cubicThetaKloostermanWeight h k c hc (residueRepresentative (3*c) x)

end CubicFirstMoment

end

end OAI
