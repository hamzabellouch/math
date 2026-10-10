import Mathlib
import OAI.Combinatorics.RamseyFive.Bounds.DensityUpper
import OAI.Combinatorics.RamseyFive.Entropy.MapFst
import OAI.Combinatorics.RamseyFive.Entropy.LevelCellSubset

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

theorem projective_expected_level_loss (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V))))
    (hp : ∀z,0 < p z→Incident z.1 z.2) (NA NB C : ℝ)
    (hNA : 0 < NA) (hNB : 0 < NB) (hC : 0 < C)
    (hA : ((support (first p)).card:ℝ) ≤ NA) (hB : ((support (second p)).card:ℝ) ≤ NB)
    (hprod : NA*NB ≤ C^2*(Nat.card K:ℝ)^5) :
    (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(4*Real.log (Nat.card K)+Real.log C+Real.log (C+1)-entropy p+
        entropy (levelLaw (first p))+entropy (levelLaw (second p))) := by
  let D : ℝ := Real.log (C+1)+(3:ℝ)/2*Real.log (Nat.card K)+(Real.log NA+Real.log NB)/2
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have he := expected_total_level_loss p NA NB D (by
    intro n hn
    let F := (support p).filter (fun z=>endpointLevels p z=n)
    let A := levelCell (first p) n.1
    let B := levelCell (second p) n.2
    have hF : F.Nonempty := positive_level_pair_support p n hn
    have hsub : F⊆(A×ˢB).filter (fun z=>Incident z.1 z.2) := level_pair_support_subset p Incident hp n
    have hI : 0 < incidences A B := Finset.card_pos.mpr (hF.mono hsub)
    have hAc : 0 < A.card := by
      obtain ⟨z,hz⟩ := hF
      exact Finset.card_pos.mpr ⟨z.1,(Finset.mem_product.mp (Finset.mem_filter.mp (hsub hz)).1).1⟩
    have hBc : 0 < B.card := by
      obtain ⟨z,hz⟩ := hF
      exact Finset.card_pos.mpr ⟨z.2,(Finset.mem_product.mp (Finset.mem_filter.mp (hsub hz)).1).2⟩
    have hAcR : (0:ℝ) < A.card := by exact_mod_cast hAc
    have hBcR : (0:ℝ) < B.card := by exact_mod_cast hBc
    have hAB : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5 :=
      (mul_le_mul (levelCell_cap _ NA hA _) (levelCell_cap _ NB hB _) (Nat.cast_nonneg _) hNA.le).trans hprod
    have hl := incidence_rectangle_log hdim A B C hC.le hAB hAc hBc hI
    have hFc : (0:ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
    have hc : (F.card:ℝ) ≤ (incidences A B:ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hf := (Real.log_le_log hFc hc).trans hl
    change Real.log (F.card:ℝ) ≤ D-(Real.log (NA/(A.card:ℝ))+Real.log (NB/(B.card:ℝ)))/2
    rw [Real.log_div hNA.ne' hAcR.ne',Real.log_div hNB.ne' hBcR.ne']
    dsimp [D]
    linarith)
  have hlog := Real.log_le_log (mul_pos hNA hNB) hprod
  rw [Real.log_mul hNA.ne' hNB.ne',Real.log_mul (pow_pos hC _).ne' (pow_pos hq _).ne',
    Real.log_pow,Real.log_pow] at hlog
  change (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(D-entropy p+entropy (levelLaw (first p))+entropy (levelLaw (second p))) at he
  dsimp only [D] at he
  apply he.trans
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

lemma Q_le_power {q d : ℕ} (hq : 2 ≤ q) : (Q q d:ℝ) ≤ (q:ℝ)^(d+1) := by
  have hg : (Q q d:ℝ)*((q:ℝ)-1)=(q:ℝ)^(d+1)-1 := by
    simpa only [Q,Nat.cast_sum,Nat.cast_pow] using geom_sum_mul (q:ℝ) (d+1)
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hn : (0:ℝ) ≤ Q q d := Nat.cast_nonneg _
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hqR)]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_entropy_cap (hdim : finrank K V=5) (p : Law (ℙ K V)) :
    entropy p ≤ 5*Real.log (Nat.card K) := by
  have h := entropy_le_log_card p
  rw [card_points (d:=4) hdim] at h
  have hQ : (0:ℝ) < Q (Nat.card K) 4 := by exact_mod_cast Q_pos (Nat.card K) 4
  have hl := Real.log_le_log hQ (Q_le_power (d:=4) (by have:=Finite.one_lt_card (α:=K);omega))
  rw [Real.log_pow] at hl
  norm_num at hl
  exact h.trans hl

omit [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma dual_entropy_cap (hdim : finrank K V=5) (p : Law (ℙ K (Dual K V))) :
    entropy p ≤ 5*Real.log (Nat.card K) := by
  have h := entropy_le_log_card p
  rw [card_hyperplanes (d:=4) hdim] at h
  have hQ : (0:ℝ) < Q (Nat.card K) 4 := by exact_mod_cast Q_pos (Nat.card K) 4
  have hl := Real.log_le_log hQ (Q_le_power (d:=4) (by have:=Finite.one_lt_card (α:=K);omega))
  rw [Real.log_pow] at hl
  norm_num at hl
  exact h.trans hl

omit [FiniteDimensional K V] in
theorem projective_level_entropy (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V)))) :
    entropy (levelLaw (first p))+entropy (levelLaw (second p)) ≤
      2*(Real.log (5*Real.log (Nat.card K)+1)+1) := by
  have hq : (1:ℝ) < Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hM : 0 < 5*Real.log (Nat.card K) := mul_pos (by norm_num) (Real.log_pos hq)
  have h₁ := endpoint_level_entropy (first p) _ hM (point_entropy_cap hdim _)
  have h₂ := endpoint_level_entropy (second p) _ hM (dual_entropy_cap hdim _)
  linarith

theorem endpoint_supports (hdim : finrank K V=5)
    (p : Law ((ℙ K V)×(ℙ K (Dual K V))))
    (hp : ∀z,0 < p z→Incident z.1 z.2) (NA NB C k δ b : ℝ)
    (hNA : 0 < NA) (hNB : 0 < NB) (hC : 0 < C) (hk : 0 < k)
    (hA : ((support (first p)).card:ℝ) ≤ NA)
    (hB : ((support (second p)).card:ℝ) ≤ NB)
    (hprod : NA*NB ≤ C^2*(Nat.card K:ℝ)^5)
    (hent : 4*Real.log (Nat.card K)-entropy p ≤ δ)
    (GA : Finset (ℙ K V)) (GB : Finset (ℙ K (Dual K V)))
    (hGA : eventMass (first p) GAᶜ ≤ b) (hGB : eventMass (second p) GBᶜ ≤ b)
    (hsmall : 2*(δ+Real.log C+Real.log (C+1)+
      2*(Real.log (5*Real.log (Nat.card K)+1)+1))/k+2*Real.exp 1*b ≤ (1:ℝ)/2) :
    ∃μ : Law (Finset (ℙ K V)), ∃ν : Law (Finset (ℙ K (Dual K V))),
      (∀A,0 < μ A→A⊆GA ∧ NA*Real.exp (-k)/2 ≤ (A.card:ℝ) ∧ (A.card:ℝ) ≤ NA) ∧
      (∀B,0 < ν B→B⊆GB ∧ NB*Real.exp (-k)/2 ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ NB) ∧
      (∀a,(∑A,μ A*(if a∈A then 1/(A.card:ℝ) else 0)) ≤ 4*Real.exp 1*first p a) ∧
      (∀a,(∑B,ν B*(if a∈B then 1/(B.card:ℝ) else 0)) ≤ 4*Real.exp 1*second p a) := by
  let T := 2*(δ+Real.log C+Real.log (C+1)+2*(Real.log (5*Real.log (Nat.card K)+1)+1))
  have hbound := projective_expected_level_loss hdim p hp NA NB C hNA hNB hC hA hB hprod
  have hlevels := projective_level_entropy hdim p
  have htotal : (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤ T := by
    dsimp only [T]
    apply hbound.trans
    linarith only [hent,hlevels]
  have hnA : 0 ≤ ∑n,levelLaw (first p) n*levelLoss (first p) NA n :=
    Finset.sum_nonneg (fun n _=>mul_nonneg ((levelLaw _).nonneg n)
      (levelLoss_nonneg _ NA hNA (levelCell_cap _ NA hA) n))
  have hnB : 0 ≤ ∑n,levelLaw (second p) n*levelLoss (second p) NB n :=
    Finset.sum_nonneg (fun n _=>mul_nonneg ((levelLaw _).nonneg n)
      (levelLoss_nonneg _ NB hNB (levelCell_cap _ NB hB) n))
  have hsA : (∑n,levelLaw (first p) n*levelLoss (first p) NA n)/k+
      2*Real.exp 1*eventMass (first p) GAᶜ ≤ (1:ℝ)/2 := by
    apply le_trans (add_le_add (div_le_div_of_nonneg_right (by linarith :
      (∑n,levelLaw (first p) n*levelLoss (first p) NA n) ≤ T) hk.le)
      (mul_le_mul_of_nonneg_left hGA (by positivity))) hsmall
  have hsB : (∑n,levelLaw (second p) n*levelLoss (second p) NB n)/k+
      2*Real.exp 1*eventMass (second p) GBᶜ ≤ (1:ℝ)/2 := by
    apply le_trans (add_le_add (div_le_div_of_nonneg_right (by linarith :
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤ T) hk.le)
      (mul_le_mul_of_nonneg_left hGB (by positivity))) hsmall
  have heA := permissible_half_mass (first p) GA NA k hNA hk (levelCell_cap _ NA hA) hsA
  have heB := permissible_half_mass (second p) GB NB k hNB hk (levelCell_cap _ NB hB) hsB
  refine ⟨goodSupportLaw (first p) GA NA k heA,goodSupportLaw (second p) GB NB k heB,?_,?_,?_,?_⟩
  · exact goodSupportLaw_bounds _ _ NA k hNA (levelCell_cap _ NA hA) heA
  · exact goodSupportLaw_bounds _ _ NB k hNB (levelCell_cap _ NB hB) heB
  · exact goodSupportLaw_domination _ _ NA k heA
  · exact goodSupportLaw_domination _ _ NB k heB

end SharpRamseyFive.ProjectiveIncidence

end OAI
