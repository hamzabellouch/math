import OAI.NumberTheory.TotientAsymptotic.LocalHeadDiscard

namespace OAI

/-! A positive family of actual candidates with head and indexed tail normality. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localNormalCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  ((tailHeadPairs x d (localRegularPrimeTuples x c L H)).filter
    (fun z => IsNormalPrime (localNormalityScale (m x)) z.2)).image
      (fun z => z.2*(∏ i,z.1 i))

lemma local_normal_candidates_subset {x c : ℝ} {d L H : ℕ} :
    localNormalCandidates x c d L H ⊆ localRegularCandidates x c d L H := by
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨z,(Finset.mem_filter.mp hz).1,rfl⟩

lemma local_normal_candidate_representation {x c : ℝ} {d L H b : ℕ}
    (hb : b ∈ localNormalCandidates x c d L H) :
    ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
      b=q*(∏ i,p i) ∧ p ∈ localRegularPrimeTuples x c L H ∧
      q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
        (x/((d*(∏ i,p i).totient:ℕ):ℝ)) ∧
      IsNormalPrime (localNormalityScale (m x)) q ∧
      ∀ i j : Fin (m x-H),i ≤ j → IsNormalPrime (localNormalityScale (m x-i.val)) (p j) := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hz,hnormal⟩ := Finset.mem_filter.mp hz
  obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hz
  exact ⟨z.1,z.2,rfl,hp,hq,hnormal,local_regular_normality hp⟩

theorem local_normal_candidate_abundance :
    ∃ c δ : ℝ,∃ L : ℕ,0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ d : ℕ,0 < d → ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(8*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localNormalCandidates x c d L H).card:ℝ) := by
  classical
  obtain ⟨c,δ,L,hc,hδ,hL,habundant⟩ := local_regular_candidate_abundance
  refine ⟨c,δ,L,hc,hδ,hL,?_⟩
  intro d hd
  have ht : Tendsto (fun x : ℝ => rho^(m x)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).comp m_tendsto
  filter_upwards [habundant d hd,local_non_normal_head_count hc d hd L]
    with H hcount hbad
  filter_upwards [hcount,hbad,
    ht.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<δ/8)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hcount hbad hsmall hB hx1
  let Q := localRegularPrimeTuples x c L H
  let F := (nonNormalHeadPairs x (localNormalityScale (m x)) d Q).image
    (fun z => z.2*(∏ i,z.1 i))
  have hQ : Q ⊆ gridPrimeTuples (localPrimeGrid x c L (m x-H)) := by
    intro p hp
    exact (Finset.mem_sdiff.mp hp).1
  have hcard : (F.card:ℝ) ≤ ((nonNormalHeadPairs x (localNormalityScale (m x)) d Q).card:ℝ) :=
    Nat.cast_le.mpr Finset.card_image_le
  have hb := hcard.trans (hbad Q hQ)
  have hcover : localRegularCandidates x c d L H ⊆ localNormalCandidates x c d L H ∪ F := by
    intro b hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    by_cases hn : IsNormalPrime (localNormalityScale (m x)) z.2
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨z,Finset.mem_filter.mpr ⟨hz,hn⟩,rfl⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hz
      exact ⟨z,Finset.mem_sigma.mpr ⟨hp,Finset.mem_filter.mpr ⟨hq,hn⟩⟩,rfl⟩
  have hcards : ((localRegularCandidates x c d L H).card:ℝ) ≤
      ((localNormalCandidates x c d L H).card:ℝ)+(F.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hscale : 0 ≤ x/(d*Real.log x) :=
    (div_pos (zero_lt_one.trans hx1) (mul_pos hdR (Real.log_pos hx1))).le
  have hb' : (F.card:ℝ) ≤ (δ/(8*d))*(x/Real.log x*G x (m x-H)) := by
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall.le hscale) (G_pos hB (m x-H)).le
    convert hh using 1
    ring
  have he : δ/(4*(d:ℝ))=δ/(8*d)+δ/(8*d) := by ring
  rw [he,add_mul] at hcount
  linarith only [hcount,hcards,hb']

end TotientAsymptotic

end

end OAI
