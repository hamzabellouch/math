import OAI.Combinatorics.SquareDifference.UniformBase

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma induction_error_absorb (N : ℕ) (hN : 0<N) (E a σ κ D : ℝ)
    (hκ : 0≤κ) (hD : 1≤D) (he : E*(N:ℝ)^(a-σ)≤κ) :
    E*(N:ℝ)^(-σ)≤κ*(D*(N:ℝ)^(-a)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ = (E*(N:ℝ)^(a-σ))*(N:ℝ)^(-a) := by
      rw [mul_assoc,←Real.rpow_add hn]
      congr 2
      ring
    _ ≤ κ*(N:ℝ)^(-a) := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hn.le _)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hD hκ
      rw [mul_one] at hh
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hn.le (-a))

lemma uniform_functional_decay {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] (hinj : Function.Injective ps)
    (hM : 2 ≤ smallModulus ps) :
    ∃a D : ℝ,0<a ∧ 1≤D ∧ ∀N : ℕ,1≤N →
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      SourcePrimeHyp ps p N → ∀A : Finset ℕ,A⊆range N → NatSquareFree A →
      setFunctional p N (powerCutoff N sourceBeta) A≤D*(N:ℝ)^(-a) := by
  let d := Fintype.card TupleVertex
  let M := smallModulus ps
  let ρ := goodSmallProbability ps
  let σ := sourceSigma d
  have hρ : 0<ρ := goodSmallProbability_pos ps hinj
  have hρ1 : ρ≤1 := goodSmallProbability_le_one ps
  have hσ : 0<σ := sourceSigma_pos d
  obtain ⟨a,ha,haσ,ha1,hθ⟩ := exists_induction_exponent M (by omega) ρ σ hρ hρ1 hσ
  let θ := (M:ℝ)^(2*a)*(1-3*ρ/4)
  change θ<1 at hθ
  let κ := (1-θ)/2
  have hκ : 0<κ := by dsimp [κ]; linarith
  have hgap : θ<1-κ := by dsimp [κ]; linarith
  obtain ⟨E,hE,hs⟩ := source_inductive_step ps hM
  have htf : Tendsto (fun N : ℕ => transferFactor d M N*θ) atTop (𝓝 θ) := by
    simpa only [one_mul] using (transferFactor_limit d M).mul_const θ
  have herr : Tendsto (fun N : ℕ => E*(N:ℝ)^(a-σ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr haσ)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
    have he : -(σ-a)=a-σ := by ring
    simpa only [he,Function.comp_def,mul_zero] using hh.const_mul E
  have ht : ∀ᶠ N : ℕ in atTop, transferFactor d M N*θ≤1-κ ∧ E*(N:ℝ)^(a-σ)≤κ := by
    filter_upwards [htf.eventually_lt_const hgap, herr.eventually_lt_const hκ] with N h1 h2
    exact ⟨h1.le,h2.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hs.and (ht.and (eventually_ge_atTop 2)))
  let D := max 1 ((T:ℝ)^(2*d)*(T:ℝ)^a)
  have hD : 1≤D := le_max_left _ _
  have hD0 : 0≤D := by linarith
  refine ⟨a,D,ha,hD,?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN J _ _ p _ hp A hA hfree
    have hN0 : 0<N := by omega
    have hinjp : Function.Injective p := fun i j hij => Sum.inr.inj (hp.injective (show extendedPrime ps p (Sum.inr i)=extendedPrime ps p (Sum.inr j) from hij))
    by_cases hnT : N≤T
    · apply (setFunctional_base p hinjp (fun j => (le_max_left _ _).trans (hp.mass j)) N hN A).trans
      exact inverse_power_base N T (2*d) hN0 hnT a D ha.le (le_max_right _ _)
    · have hlarge := hT N (by omega)
      have hh := hlarge.1 p hp.injective hp.lower hp.mass hp.reflection hp.coprime hp.exceptional hp.cover
        a ha.le ha1 D hD0 (fun n hn hnN A' hA' hf => ih n hnN hn p (hp.mono hnN.le) A' hA' hf)
        A hA hfree
      apply hh.trans
      have hr := induction_error_absorb N hN0 E a σ κ D hκ.le hD hlarge.2.1.2
      have hn : 0≤D*(N:ℝ)^(-a) := mul_nonneg hD0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hc := mul_le_mul_of_nonneg_right hlarge.2.1.1 hn
      change E*(N:ℝ)^(-σ)+transferFactor d M N*D*(N:ℝ)^(-a)*θ≤D*(N:ℝ)^(-a)
      calc
        _ = E*(N:ℝ)^(-σ)+(transferFactor d M N*θ)*(D*(N:ℝ)^(-a)) := by ring
        _ ≤ κ*(D*(N:ℝ)^(-a))+(1-κ)*(D*(N:ℝ)^(-a)) := add_le_add hr hc
        _ = _ := by ring

end SquareDifference

end

end OAI
