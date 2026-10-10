import OAI.NumberTheory.DirichletL.CenteredExceptionalCount

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CenteredExceptionalCount IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=>sixthRemainder (Ideal.span {z}))

lemma lowGramRemainders_nonzero (F : Finset O) (R : Id) (hR : R∈lowGramRemainders F) : R≠0 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
  exact sixthRemainder_ne_zero _

theorem lowGramRemainders_card (F : Finset O) (G : Id)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0) :
    (lowGramRemainders F).card≤6^(primeSupport G).card := by
  have hlt (R : lowGramRemainders F) (P : Id) : valuation R.val P<6 := by
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp R.property
    rw [←he]
    exact sixthRemainder_valuation_lt _ _
  let code : lowGramRemainders F→(primeSupport G→Fin 6) := fun R P=>⟨valuation R.val P.val,hlt R P.val⟩
  have hinj : Function.Injective code := by
    intro R T he
    apply Subtype.ext
    apply ideal_eq_of_valuation_eq (lowGramRemainders_nonzero F R.val R.property)
      (lowGramRemainders_nonzero F T.val T.property)
    intro P
    by_cases hp : P∈primeSupport G
    · exact congrArg Fin.val (congrFun he ⟨P,hp⟩)
    · obtain ⟨r,hr,her⟩ := Finset.mem_image.mp R.property
      obtain ⟨t,ht,het⟩ := Finset.mem_image.mp T.property
      rw [←her,←het,sixthRemainder_valuation,sixthRemainder_valuation,hres r hr P hp,hres t ht P hp]
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hh

theorem lowGramExceptional_raw_count (F : Finset O) (G : Id) (H : ℝ) (hH : 0≤H)
    (hF : ∀z∈F,z≠0)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)
    (hN : ∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H) :
    (F.card:ℝ)≤768*(6:ℝ)^(primeSupport G).card*H^(1/6:ℝ) := by
  have hh := element_count_remainder_family F (lowGramRemainders F)
    (lowGramRemainders_nonzero F) H hH hF (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hN
  calc
    _ ≤ ∑R∈lowGramRemainders F,768*(H/(Ideal.absNorm R:ℝ))^(1/6:ℝ) := hh
    _ ≤ ∑_R∈lowGramRemainders F,768*H^(1/6:ℝ) := by
      apply Finset.sum_le_sum
      intro R hR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (div_nonneg hH (Nat.cast_nonneg _)) _ (by norm_num)
      exact div_le_self hH (norm_one_le (lowGramRemainders_nonzero F R hR))
    _ = (lowGramRemainders F).card*(768*H^(1/6:ℝ)) := by simp
    _ ≤ ((6:ℝ)^(primeSupport G).card)*(768*H^(1/6:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGramRemainders_card F G hres
    _ = _ := by ring

theorem lowGramExceptional_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀G : Id,G≠0→∀F : Finset O,∀H : ℝ,0≤H→
      (∀z∈F,z≠0)→
      (∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)→
      (∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H)→
      (F.card:ℝ)≤C*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/3) (by positivity)
  refine ⟨768*C^3,by positivity,?_⟩
  intro G hG F H hH hF hres hN
  have hp : (6:ℝ)^(primeSupport G).card≤C^3*(Ideal.absNorm G:ℝ)^ε := by
    calc
      _ ≤ ((2:ℝ)^3)^(primeSupport G).card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2:ℝ)^(primeSupport G).card)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (C*(Ideal.absNorm G:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) (hb G hG) 3
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm G))]
        congr 2
        norm_num
  apply (lowGramExceptional_raw_count F G H hH hF hres hN).trans
  calc
    _ ≤ 768*(C^3*(Ideal.absNorm G:ℝ)^ε)*H^(1/6:ℝ) := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
