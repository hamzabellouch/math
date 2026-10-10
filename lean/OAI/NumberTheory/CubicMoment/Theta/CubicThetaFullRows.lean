import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHeightReduction

namespace OAI

/-! Primitive rows of the full Eisenstein modular group. Their proper
height function gives the full-group reduction needed for a finite cusp
cover of the principal level-three quotient. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

@[ext] structure CubicThetaPrimitiveRow where
  c : Eisenstein
  d : Eisenstein
  coprime : IsCoprime c d

def cubicThetaFullComplex : SL(2,Eisenstein) →* SL(2,ℂ) :=
  Matrix.SpecialLinearGroup.map (eisensteinRing.subtype : Eisenstein →+* ℂ)

def cubicThetaPrimitiveRow (g : SL(2,Eisenstein)) : CubicThetaPrimitiveRow :=
  ⟨g 1 0,g 1 1,⟨-g 0 1,g 0 0,by
    have h : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
    linear_combination h⟩⟩

lemma cubicThetaPrimitiveRow_surjective : Function.Surjective cubicThetaPrimitiveRow := by
  intro r
  obtain ⟨a,b,h⟩ := r.coprime
  let g : SL(2,Eisenstein) := ⟨!![b,-a;r.c,r.d],by
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩
  exact ⟨g,by ext <;> rfl⟩

def CubicThetaPrimitiveRow.denominator (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) : ℝ :=
  Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2

def CubicThetaPrimitiveRow.height (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) : ℝ :=
  p.2/r.denominator p

lemma CubicThetaPrimitiveRow.denominator_pos (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0<r.denominator p := by
  rcases r.coprime.ne_zero_or_ne_zero with hc | hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))
  · by_cases hc : r.c=0
    · simpa [CubicThetaPrimitiveRow.denominator,hc,norm] using Complex.normSq_pos.mpr
        (show (r.d:ℂ)≠0 from fun h => hd (Subtype.ext h))
    · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
        (mul_pos (norm_pos_of_ne_zero hc) (sq_pos_of_pos hp))

lemma CubicThetaPrimitiveRow.height_pos (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : 0<r.height p := div_pos hp (r.denominator_pos hp)

lemma cubicThetaPrimitiveRow_height (g : SL(2,Eisenstein)) (p : ℂ × ℝ) :
    (cubicThetaPrimitiveRow g).height p=(cubicThetaMobius (cubicThetaFullComplex g) p).2 := rfl

lemma CubicThetaPrimitiveRow.norm_sum_bound (r : CubicThetaPrimitiveRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    norm r.c+norm r.d ≤ (2+(1+2*Complex.normSq p.1)/p.2^2)*r.denominator p := by
  let D := r.denominator p
  have hc : norm r.c ≤ D/p.2^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    dsimp [D,CubicThetaPrimitiveRow.denominator]
    linarith [Complex.normSq_nonneg ((r.c:ℂ)*p.1+r.d)]
  have hd : norm r.d ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+2*norm r.c*Complex.normSq p.1 := by
    have h : Complex.normSq (((r.c:ℂ)*p.1+r.d)-(r.c:ℂ)*p.1) ≤
        2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+2*Complex.normSq ((r.c:ℂ)*p.1) := by
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
      nlinarith [sq_nonneg (((r.c:ℂ)*p.1+r.d).re+((r.c:ℂ)*p.1).re),
        sq_nonneg (((r.c:ℂ)*p.1+r.d).im+((r.c:ℂ)*p.1).im)]
    rw [add_sub_cancel_left,Complex.normSq_mul] at h
    simpa only [norm,mul_assoc] using h
  calc
    _ ≤ 2*Complex.normSq ((r.c:ℂ)*p.1+r.d)+(1+2*Complex.normSq p.1)*norm r.c := by linarith
    _ ≤ 2*D+(1+2*Complex.normSq p.1)*(D/p.2^2) := by
      apply add_le_add
      · dsimp [D,CubicThetaPrimitiveRow.denominator]
        linarith [mul_nonneg (norm_nonneg r.c) (sq_nonneg p.2)]
      · exact mul_le_mul_of_nonneg_left hc (by linarith [Complex.normSq_nonneg p.1])
    _ = _ := by ring

lemma cubicThetaPrimitiveRow_height_superlevel_finite {p : ℂ × ℝ} (hp : 0<p.2)
    {a : ℝ} (ha : 0<a) : Set.Finite {r : CubicThetaPrimitiveRow | a ≤ r.height p} := by
  let K := 2+(1+2*Complex.normSq p.1)/p.2^2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (by norm_num) (div_nonneg (by linarith [Complex.normSq_nonneg p.1]) (sq_nonneg _))
  let B := K*(p.2/a)
  have hfin : Set.Finite {r : CubicThetaPrimitiveRow | norm r.c ≤ B ∧ norm r.d ≤ B} := by
    have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
      intro r t he
      exact CubicThetaPrimitiveRow.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2
    exact ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  apply hfin.subset
  intro r hr
  have hD : r.denominator p ≤ p.2/a := by
    apply (le_div_iff₀ ha).mpr
    have h := (le_div_iff₀ (r.denominator_pos hp)).mp hr
    nlinarith
  have hb : norm r.c+norm r.d ≤ B :=
    (r.norm_sum_bound hp).trans (mul_le_mul_of_nonneg_left hD hK)
  exact ⟨by linarith [norm_nonneg r.d],by linarith [norm_nonneg r.c]⟩

theorem cubicThetaFullGroup_exists_max_height {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ g : SL(2,Eisenstein), ∀ h : SL(2,Eisenstein),
      (cubicThetaMobius (cubicThetaFullComplex h) p).2 ≤
        (cubicThetaMobius (cubicThetaFullComplex g) p).2 := by
  let r0 := cubicThetaPrimitiveRow (1 : SL(2,Eisenstein))
  let S : Set CubicThetaPrimitiveRow := {r | r0.height p ≤ r.height p}
  have hfin : S.Finite := cubicThetaPrimitiveRow_height_superlevel_finite hp (r0.height_pos hp)
  have hne : hfin.toFinset.Nonempty := ⟨r0,by simp [S]⟩
  obtain ⟨r,hr,hmax⟩ := hfin.toFinset.exists_max_image (fun r => r.height p) hne
  obtain ⟨g,rfl⟩ := cubicThetaPrimitiveRow_surjective r
  refine ⟨g,?_⟩
  intro h
  change (cubicThetaPrimitiveRow h).height p ≤ (cubicThetaPrimitiveRow g).height p
  by_cases hh : r0.height p ≤ (cubicThetaPrimitiveRow h).height p
  · exact hmax _ (by simpa [S] using hh)
  · exact (lt_of_not_ge hh).le.trans (by simpa [S] using hr)

end CubicFirstMoment

end

end OAI
