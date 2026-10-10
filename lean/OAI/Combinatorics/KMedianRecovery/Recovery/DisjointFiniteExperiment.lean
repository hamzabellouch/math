import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ZeroClasses

namespace OAI

namespace MetricKMedianRecovery.RoundedAssembly
open LocalSearch Sampling FiniteSampling IntegralAssembly

theorem disjoint_finite_experiment : ∃ v : ℚ, 0 < v ∧ ∃ Nstar : ℕ, 1 ≤ Nstar ∧
    ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [PseudoMetricSpace V] [LinearOrder V] [Fintype V],
    ∀ (F D : Finset V) (k : ℕ) (ζ : ℝ),
    D.Nonempty → 0 < k → k ≤ F.card → Disjoint D F → 0 < ζ →
    let C := Rounding.cap D.card (gamma/16)
    let L0 := countBound (commonL v Nstar D.card C)
    let n := repetitions c L0 ζ
    ∃ run : RecoverySeed D F C L0 (D.card*C) n → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 6*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma/2)*optimum F D k) ∧
      average (fun seed => cost D (run seed)) ≤
        ((2-gamma/2)+6*ζ)*optimum F D k := by
  classical
  obtain ⟨v,hv,Nstar,hNstar,c,hc,H⟩ := rounded_calls
  refine ⟨v,hv,Nstar,hNstar,c,hc,?_⟩
  intro V _ _ _ F D k ζ hD hk hkF hDF hζ
  let C := Rounding.cap D.card (gamma/16)
  let L0 := countBound (commonL v Nstar D.card C)
  let n := repetitions c L0 ζ
  let Ω := RecoverySeed D F C L0 (D.card*C) n
  have hF : F.Nonempty := Finset.card_pos.mp (hk.trans_le hkF)
  have hopt0 := optimum_nonneg F D k
  have hcoef : 0 ≤ 2-gamma/2 := by linarith [gamma_lt_one]
  have hex : ∃ run : Ω → Finset V,
      (∀ seed, run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k ∧
        cost D (run seed) ≤ 6*optimum F D k) ∧
      1-ζ ≤ probability (fun seed => cost D (run seed) ≤ (2-gamma/2)*optimum F D k) := by
    by_cases hz : zeroClasses D ⊆ zeroClasses F ∧ (zeroClasses D).card ≤ k
    · obtain ⟨S,hSF,hS,hSc,hcost⟩ := zero_classes_solution F D hD hz.1
      have hzero := (optimum_zero_iff F D hF hD k hk).mpr hz
      refine ⟨fun _ => S,fun _ => ⟨hSF,hS,hSc.trans hz.2,?_⟩,?_⟩
      · rw [hcost,hzero]; norm_num
      · dsimp only
        rw [hcost,hzero]
        simp only [mul_zero,le_refl,probability,ite_true,average_const]
        linarith
    · let G := {g : V × V // g.1 ∈ D ∧ g.2 ∈ F ∧ 0 < dist g.1 g.2}
      have hcalls (g : G) := H V F D k ζ (dist g.val.1 g.val.2) hD hk hkF hDF hζ g.property.2.2
      let call (g : G) : Ω → Finset V := Classical.choose (hcalls g)
      have hcall (g : G) := Classical.choose_spec (hcalls g)
      obtain ⟨f,hf⟩ := hF
      let run (seed : Ω) := enumeratedBest (cost D) {f} (fun g : G => call g seed)
      have hfeas (seed : Ω) : run seed ⊆ F ∧ (run seed).Nonempty ∧ (run seed).card ≤ k := by
        rcases enumeratedBest_mem (cost D) {f} (fun g : G => call g seed) with he | ⟨g,he⟩
        · dsimp only [run]
          rw [he]
          exact ⟨Finset.singleton_subset_iff.mpr hf,Finset.singleton_nonempty _,by simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr hk)⟩
        · dsimp only [run]
          rw [he]
          exact (hcall g).1 seed
      have hmin (seed : Ω) (g : G) : cost D (run seed) ≤ cost D (call g seed) :=
        (enumeratedBest_le (cost D) {f} (fun g : G => call g seed)).2 g
      obtain ⟨O,hOF,hO,hOk,hOcost⟩ := optimum_attained F D ⟨f,hf⟩ k hk
      have hP : 0 < cost D O := by
        rw [hOcost]
        exact lt_of_le_of_ne hopt0 (Ne.symm (fun he => hz ((optimum_zero_iff F D ⟨f,hf⟩ hD k hk).mp he)))
      obtain ⟨p,hp,i,hi,hM,hMP,hPM⟩ := Rounding.largest_guess D O F hD hO hOF hP
      let g : G := ⟨(p,i),hp,hi,hM⟩
      have hgood := (hcall g).2 O hOF hO hOk
      have heps : 0 < gamma/16 := div_pos gamma_pos (by norm_num)
      have heps1 : gamma/16 < 1 := by linarith [gamma_lt_one]
      have htransfer (seed : Ω) (A : ℝ) (hA : 0 ≤ A) (hA5 : A ≤ 5)
          (hcost : (Rounding.cost ((gamma/16)*dist p i/D.card) C D (call g seed):ℝ) ≤
            A*(Rounding.cost ((gamma/16)*dist p i/D.card) C D O:ℝ)) :
          cost D (call g seed) ≤ A*(1+gamma/16)*cost D O :=
        Rounding.factor_transfer D O (call g seed) hO ((hcall g).1 seed).2.1 hD.card_pos
          (gamma/16) (dist p i) A heps heps1 hM hMP hPM hA hA5 hcost
      refine ⟨run,?_,?_⟩
      · intro seed
        refine ⟨(hfeas seed).1,(hfeas seed).2.1,(hfeas seed).2.2,?_⟩
        calc
          cost D (run seed) ≤ cost D (call g seed) := hmin seed g
          _ ≤ 5*(1+gamma/16)*cost D O := htransfer seed 5 (by norm_num) le_rfl (hgood.1 seed)
          _ ≤ 6*cost D O := mul_le_mul_of_nonneg_right rounded_fallback_factor hP.le
          _ = _ := by rw [hOcost]
      · refine hgood.2.trans (probability_mono (fun seed hs => ?_))
        calc
          cost D (run seed) ≤ cost D (call g seed) := hmin seed g
          _ ≤ (2-gamma)*(1+gamma/16)*(1+gamma/16)*cost D O :=
            htransfer seed _ successful_factor_nonneg successful_factor_le_five hs
          _ ≤ (2-gamma/2)*cost D O := mul_le_mul_of_nonneg_right rounded_successful_factor hP.le
          _ = _ := by rw [hOcost]
  obtain ⟨run,hfeas,hprob⟩ := hex
  refine ⟨run,hfeas,hprob,?_⟩
  have hfail : probability (fun seed => (2-gamma/2)*optimum F D k < cost D (run seed)) ≤ ζ := by
    rw [show (fun seed => (2-gamma/2)*optimum F D k < cost D (run seed)) =
      (fun seed => ¬cost D (run seed) ≤ (2-gamma/2)*optimum F D k) from by
        funext seed; exact propext not_le.symm,probability_compl]
    linarith
  calc
    average (fun seed => cost D (run seed)) ≤ (2-gamma/2)*optimum F D k +
        probability (fun seed => (2-gamma/2)*optimum F D k < cost D (run seed))*(6*optimum F D k) :=
      average_le_threshold_add_failure _ (mul_nonneg hcoef hopt0) (fun seed => (hfeas seed).2.2.2)
    _ ≤ (2-gamma/2)*optimum F D k + ζ*(6*optimum F D k) := by gcongr
    _ = _ := by ring

end MetricKMedianRecovery.RoundedAssembly
namespace MetricKMedianRecovery.IndexedCopies
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma marked_disjoint (D F : Finset V) : Disjoint (marked false D) (marked true F) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨x,hx,hex⟩ := Finset.mem_map.mp hp
  obtain ⟨y,hy,hey⟩ := Finset.mem_map.mp hq
  have he := congrArg Prod.snd (hex.trans hey.symm)
  change false = true at he
  cases he

lemma optimum_marked (F D : Finset V) (hF : F.Nonempty) (k : ℕ) (hk : 0 < k) :
    @optimum (V × Bool) metric (marked true F) (marked false D) k = optimum F D k := by
  classical
  apply le_antisymm
  · obtain ⟨O,hOF,hO,hOk,hcost⟩ := optimum_attained F D hF k hk
    have hbound := @optimum_le (V × Bool) metric (marked true F) (marked false D) (marked true O) k
      (marked_subset true hOF) ((marked_nonempty true O).mpr hO) (by simpa only [marked_card] using hOk)
    rw [cost_marked,hcost] at hbound
    exact hbound
  · obtain ⟨O,hOF,hO,hOk,hcost⟩ := @optimum_attained (V × Bool) metric
      (marked true F) (marked false D) ((marked_nonempty true F).mpr hF) k hk
    obtain ⟨T,hTF,he,hcard⟩ := project_set F O hOF
    have hT : T.Nonempty := (marked_nonempty true T).mp (he.symm ▸ hO)
    have hTk : T.card ≤ k := hcard.trans_le hOk
    have hct : cost D T = @cost (V × Bool) metric (marked false D) O := by
      rw [←he,cost_marked]
    exact (optimum_le F D T k hTF hT hTk).trans_eq (hct.trans hcost)

end MetricKMedianRecovery.IndexedCopies

end OAI
