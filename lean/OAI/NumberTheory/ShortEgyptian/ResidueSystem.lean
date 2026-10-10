import OAI.NumberTheory.ShortEgyptian.ResidueAssembly

namespace OAI

universe uA

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

structure ResidueSystem (S : ℝ) (C : ℕ) where
  M : ℕ
  M_lower : Real.exp S < (M:ℝ)
  M_upper : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S)
  binary_dvd : 2^binaryExponent S ∣ M
  t : ℕ → (Fin (scaleM S) → Bool) → ℕ
  t_pos : ∀ j i, 0 < t j i
  t_dvd : ∀ j i, t j i ∣ M
  bad : ℕ → Finset ℕ
  bad_card : ∀ j, j < depth S → (bad j).card ≤ level S j*Real.exp (-(1/1000:ℝ)*scaleM S)
  good_residues : ∀ j, j < depth S → ∀ u ∈ scaleInterval (level S j) (scaleRho S), u ∉ bad j →
    scaleRho S*Fintype.card (Fin (scaleM S) → Bool)/2 ≤
      ((univ.filter fun i => (residue (levelMultiplier S C j*t j i) u
        (quotient (levelMultiplier S C j*t j i) u):ℝ) ≤ level S (j+1)).card:ℝ)
  terminal : ∀ u : ℕ, S^100000 < (u:ℝ) → (u:ℝ) ≤ Real.exp (scaleM S:ℝ) →
    ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      (residue t u (quotient t u):ℝ) ≤ (u:ℝ)^((9999/10000:ℝ))

lemma terminal_interval (S : ℝ) (h : ListScale S) (u : ℕ)
    (hu : u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊) :
    3 ≤ u ∧ 100000*Real.log S ≤ Real.log u ∧ Real.log u ≤ (scaleM S:ℝ) := by
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hu
  have huR : S^100000 < (u:ℝ) := Nat.lt_of_floor_lt (by omega)
  have hpow : S ≤ S^100000 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [h.two_le] : (1:ℝ)≤S) (by norm_num : 1 ≤ 100000)
  have hu2 : (2:ℝ) < u := h.two_le.trans hpow |>.trans_lt huR
  have huN : 3 ≤ u := by exact_mod_cast (show (2:ℝ)<u from hu2)
  have hu0 : 0 < (u:ℝ) := by linarith
  refine ⟨huN,?_,(Real.log_le_iff_le_exp hu0).mpr ((Nat.cast_le.mpr hhi).trans (Nat.floor_le (Real.exp_nonneg _)))⟩
  have hh := Real.log_le_log (pow_pos h.S_pos 100000) huR.le
  rw [Real.log_pow] at hh
  norm_num at hh
  exact hh

lemma assemble_residueSystem {A : Type uA} (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S))
    (p₀ : Fin (scaleM S) → ℕ) (hp₀ : ∀ j, (p₀ j).Prime) (hinj : Function.Injective p₀)
    (hp₀max : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp₀min : ∀ j, S^100 ≤ (p₀ j:ℝ))
    (p : A → ℕ) (hp : ∀ x, (p x).Prime) (hpmax : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (f : Fin 1000 → (Fin (scaleM S) × Bool) → A)
    (hf : ∀ j, j < depth S → level S j ≤ Real.exp S →
      ((badLevel (fun I => sampleProduct p I (f 0)) 1 (level S j) (scaleRho S)).card:ℝ) ≤
        level S j*Real.exp (-(1/1000:ℝ)*scaleM S))
    (hterm : ∀ u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊,
      ∃ i, ¬FourierBad (fun I => sampleProduct p I (f i)) 1 u
        (Real.exp (-(1/10000:ℝ)*Real.log u))) :
    Nonempty (ResidueSystem S C) := by
  let M := auxiliaryDenominator (binaryExponent S) p₀ p f
  have hp₀pos (j : Fin (scaleM S)) : 0 < p₀ j := (hp₀ j).pos
  have hppos (x : A) : 0 < p x := (hp x).pos
  have hmcard : (Fintype.card (Fin (scaleM S)):ℝ) ≤ S/Real.log S := by
    simpa only [Fintype.card_fin] using h.m_bounds.2.1
  have hMlo : Real.exp S < (M:ℝ) := auxiliary_lower S _ p₀ p f h.S_pos (by linarith [h.log_one])
    (by simpa only [Fintype.card_fin] using h.m_bounds.1) hp₀min hp₀pos hppos
  have hMhi : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S) := auxiliary_upper S _ p₀ p f h.two_le
    (by linarith [h.log_one]) hmcard hp₀max hpmax
    (binary_power_upper S h.log_one h.log_bound)
  let t (j : ℕ) : (Fin (scaleM S) → Bool) → ℕ :=
    if Real.exp S < level S j then deterministicProduct p₀ else fun I => sampleProduct p I (f 0)
  have htpos (j : ℕ) (I : Fin (scaleM S) → Bool) : 0 < t j I := by
    dsimp [t]
    split
    · exact deterministicProduct_pos p₀ hp₀pos I
    · exact sampleProduct_pos p hppos (f 0) I
  have htdvd (j : ℕ) (I : Fin (scaleM S) → Bool) : t j I ∣ M := by
    dsimp [t]
    split
    · exact deterministic_dvd_auxiliary _ p₀ p f I
    · exact sample_dvd_auxiliary _ p₀ p f 0 I
  let B (j : ℕ) := badLevel (t j) (levelMultiplier S C j) (level S j) (scaleRho S)
  have hB (j : ℕ) (hj : j < depth S) : ((B j).card:ℝ) ≤ level S j*Real.exp (-(1/1000:ℝ)*scaleM S) := by
    by_cases hx : Real.exp S < level S j
    · dsimp only [B,t,levelMultiplier]
      simp only [ite_eq_left hx]
      exact high_badLevel S (level S j) C p₀ hp₀ hinj (Fintype.card_fin _)
        hp₀max h.two_le h.log_one h.m_hundred h.reciprocal_power
        h.reciprocal_const hx.le (by simpa only [level_zero] using level_antitone S (Nat.zero_le j)) hClo hChi
    · simpa only [B,t,levelMultiplier,ite_eq_right hx] using hf j hj (le_of_not_gt hx)
  have hC : 0 < C := by
    have hh : (0:ℝ)<C := (Real.exp_pos _).trans_le hClo
    exact_mod_cast hh
  refine ⟨⟨M,hMlo,hMhi,two_pow_dvd_auxiliary _ p₀ p f,t,htpos,htdvd,B,hB,?_,?_⟩⟩
  · intro j _hj u hu hbad
    have hu' := scaleInterval_mem (level_pos S j).le hu
    have hgood : ¬FourierBad (t j) (levelMultiplier S C j) u (scaleRho S) := by
      intro hbad'
      exact hbad (mem_filter.mpr ⟨hu,hbad'⟩)
    have hc := fourier_good_residues (t j) (levelMultiplier S C j) u
      (levelMultiplier_pos S C j hC) hu'.1 (htpos j) (scaleRho S) (scaleRho_pos S) h.rho_small hgood
    apply hc.trans
    apply Nat.cast_le.mpr
    apply card_le_card
    intro I hI
    refine mem_filter.mpr ⟨mem_univ I,?_⟩
    have hh := (mem_filter.mp hI).2
    rw [level_succ]
    exact hh.le.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu'.2.2 (scaleRho_pos S).le)
  · intro u hu huhi
    have huU : u ∈ Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊ := mem_Icc.mpr ⟨by have hh := (Nat.floor_lt (by positivity : 0 ≤ S^100000)).mpr hu; omega,
      Nat.le_floor huhi⟩
    obtain ⟨i,hi⟩ := hterm u huU
    have huinfo := terminal_interval S h u huU
    have hu0 : 0 < u := by omega
    have hδ := Real.exp_pos (-(1/10000:ℝ)*Real.log u)
    have hc := fourier_good_residues (fun I => sampleProduct p I (f i)) 1 u (by norm_num) hu0
      (sampleProduct_pos p hppos (f i)) _ hδ (h.terminal_small u huinfo.2.1) hi
    have hcardpos : 0 < (Fintype.card (Fin (scaleM S) → Bool):ℝ) := by exact_mod_cast Fintype.card_pos
    have hne : (univ.filter fun I => (residue (1*sampleProduct p I (f i)) u
        (quotient (1*sampleProduct p I (f i)) u):ℝ) < Real.exp (-(1/10000:ℝ)*Real.log u)*u).Nonempty := by
      apply card_pos.mp
      exact_mod_cast (div_pos (mul_pos hδ hcardpos) (by norm_num : (0:ℝ)<2)).trans_le hc
    obtain ⟨I,hI⟩ := hne
    refine ⟨sampleProduct p I (f i),sampleProduct_pos p hppos (f i) I,
      sample_dvd_auxiliary _ p₀ p f i I,?_⟩
    have hh := (mem_filter.mp hI).2
    simp only [one_mul] at hh
    apply hh.le.trans_eq
    have huR : 0 < (u:ℝ) := by exact_mod_cast hu0
    rw [Real.rpow_def_of_pos huR,←Real.exp_log huR,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    ring

lemma exists_residueSystem (S : ℝ) (h : ListScale S) (C : ℕ)
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    Nonempty (ResidueSystem S C) := by
  let P := scalePrimes S
  have hP : S^99 ≤ (P.card:ℝ) := scalePrimes_card S h.two_le h.log_one
    (by linarith [h.log_bound,h.log_large])
  have hmP : scaleM S ≤ Fintype.card P := by
    have hpow : S ≤ S^99 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith [h.two_le] : (1:ℝ)≤S) (by norm_num : 1 ≤ 99)
    have hh : (scaleM S:ℝ) ≤ Fintype.card P := by simpa using h.m_bounds.2.2.trans (hpow.trans hP)
    exact_mod_cast hh
  have hPpos : 0 < P.card := by simpa using h.m_pos.trans_le hmP
  obtain ⟨p',hp'⟩ := P.card_pos.mp hPpos
  have : Nonempty P := ⟨⟨p',hp'⟩⟩
  let p : P → ℕ := Subtype.val
  have hp (x : P) := (scalePrimes_mem S x x.property).1
  have hpmax (x : P) := (scalePrimes_mem S x x.property).2.2
  have hpmin (x : P) := (scalePrimes_mem S x x.property).2.1
  let e : Fin (scaleM S) → P := fun j => (Fintype.equivFin P).symm ⟨j.val,lt_of_lt_of_le j.isLt hmP⟩
  let p₀ : Fin (scaleM S) → ℕ := fun j => p (e j)
  have hinj : Function.Injective p₀ := by
    intro i j hij
    have he : e i = e j := Subtype.ext hij
    have hh := (Fintype.equivFin P).symm.injective he
    exact Fin.ext (congrArg (fun x : Fin (Fintype.card P) => x.val) hh)
  let D := {j : Fin (depth S) // level S j ≤ Real.exp S}
  let X : D → ℝ := fun j => level S j.val
  let U := Icc (⌊S^100000⌋₊+1) ⌊Real.exp (scaleM S:ℝ)⌋₊
  have hX (j : D) : Real.exp (⌊S/Real.log S⌋₊:ℝ) ≤ X j ∧ X j ≤ Real.exp S :=
    ⟨((level_before_depth S h.m_pos j.val).mp j.val.isLt).le,j.property⟩
  have hsmall : (Fintype.card D:ℝ)*Real.exp (-(1/250:ℝ)*(scaleM S:ℝ)) < 1/2 := by
    have hd : Fintype.card D ≤ depth S := by
      simpa only [Fintype.card_fin] using (Fintype.card_subtype_le (fun j : Fin (depth S) => level S j ≤ Real.exp S))
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) (Real.exp_nonneg _)).trans_lt h.depth_tail
  obtain ⟨f,hf,hterm⟩ := choose_random_lists S (J := Fin (scaleM S)) (Fintype.card_fin _)
    h.log_one (by linarith [h.log_bound,h.log_large]) p hp Subtype.val_injective hpmax
    (by simpa using hP) h.m_fourier h.m_bounds.2.2 X hX U (terminal_interval S h) hsmall
  exact assemble_residueSystem S h C hClo hChi p₀ (fun j => hp (e j)) hinj
    (fun j => hpmax (e j)) (fun j => hpmin (e j)) p hp hpmax f
    (fun j hj hx => hf ⟨⟨j,hj⟩,hx⟩) hterm

end ShortEgyptian

end OAI
