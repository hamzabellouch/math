import OAI.Probability.BenjaminiSchramm.GhostField
import OAI.Probability.BenjaminiSchramm.BlockExposure

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V : Type*}

lemma ghost_avoidance_exterior_factor (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ m, ({m | Disjoint (S : Set V) m} : Set (Set V)).indicator
      (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)) m
      ∂ghostFieldLaw h w) =
        ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) *
          ∫⁻ m, F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)
            ∂ghostFieldLaw h w := by
  let A := {m : Set V | Disjoint (S : Set V) m}
  have hA : MeasurableSet A := by
    rw [show A = ⋂ v ∈ S, {m | v ∉ m} from by ext m; simp [A,Set.disjoint_left]]
    exact S.measurableSet_biInter fun v _ => (measurable_set_mem v).setOf.compl
  have hd : DependsOn (fun m => m ∈ A) (S : Set V) := by
    intro m n hmn
    apply propext
    simp only [A, Set.disjoint_left]
    exact ⟨fun hm v hv hn => hm hv ((hmn v hv).to_iff.mpr hn),
      fun hn v hv hm => hn hv ((hmn v hv).to_iff.mp hm)⟩
  have hforce : DependsOn
      (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m))
      (S : Set V)ᶜ := by
    intro m n hmn
    apply congrArg F
    unfold CriticalPercolation.BernoulliProduct.forceOn
    funext v
    by_cases hv : v ∈ (S : Set V)
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]
      exact hmn v hv
  have he := CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh
    (fun v => ghostRate h (w v)) (S : Set V) A hA hd
    (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m))
    (hF.comp (CriticalPercolation.BernoulliProduct.measurable_forceOn _ _)) hforce
  change _ = ghostFieldLaw h w A * _ at he
  rw [ghostFieldLaw_avoid_finset] at he
  exact he

lemma ghost_avoidance_upper (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V → ℝ≥0∞) (hF : Measurable F) (hmono : Monotone F) :
    (∫⁻ m, if Disjoint (S : Set V) m then F m else 0 ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) *
        ∫⁻ m, F m ∂ghostFieldLaw h w := by
  have heq (m : Set V) (hm : Disjoint (S : Set V) m) :
      CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m = m := by
    ext v
    by_cases hv : v ∈ (S : Set V)
    · have hvm : v ∉ m := fun h => Set.disjoint_left.mp hm hv h
      simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hv,hvm]
    · simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hv]
  calc
    _ = ∫⁻ m, ({m | Disjoint (S : Set V) m} : Set (Set V)).indicator
        (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)) m
        ∂ghostFieldLaw h w := by
      apply lintegral_congr
      intro m
      by_cases hm : Disjoint (S : Set V) m <;> simp [Set.indicator,hm,heq m]
    _ = _ := ghost_avoidance_exterior_factor h w S F hF
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro m
      apply hmono
      intro v hv
      by_cases hvS : v ∈ (S : Set V)
      · simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hvS] at hv
      · simpa [CriticalPercolation.BernoulliProduct.mem_forceOn,hvS] using hv

theorem two_ghost_avoidance_upper (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V × Set V → ℝ≥0∞) (hF : Measurable F)
    (hmono : ∀ m m', m ⊆ m' → ∀ n n', n ⊆ n' → F (m,n) ≤ F (m',n')) :
    (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n
      then F (m,n) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) ^ 2 *
        ∫⁻ m, ∫⁻ n, F (m,n) ∂ghostFieldLaw h w ∂ghostFieldLaw h w := by
  let c := ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ)))
  let H := fun m => ∫⁻ n, F (m,n) ∂ghostFieldLaw h w
  have hH : Measurable H := hF.lintegral_prod_right'
  have hHm : Monotone H := by
    intro m m' hmm
    exact lintegral_mono fun n => hmono m m' hmm n n le_rfl
  calc
    _ ≤ ∫⁻ m, if Disjoint (S : Set V) m then c * H m else 0 ∂ghostFieldLaw h w := by
      apply lintegral_mono
      intro m
      by_cases hm : Disjoint (S : Set V) m
      · simp only [hm, true_and, ite_true]
        exact ghost_avoidance_upper h w S (fun n => F (m,n))
          (hF.comp (measurable_const.prodMk measurable_id))
          (fun n n' hnn => hmono m m le_rfl n n' hnn)
      · simp only [hm, false_and, ite_false, lintegral_zero, le_refl]
    _ = c * ∫⁻ m, if Disjoint (S : Set V) m then H m else 0 ∂ghostFieldLaw h w := by
      have heq (m : Set V) : (if Disjoint (S : Set V) m then c * H m else 0) =
          c * (if Disjoint (S : Set V) m then H m else 0) := by split_ifs <;> simp
      simp_rw [heq]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ c * (c * ∫⁻ m, H m ∂ghostFieldLaw h w) :=
      mul_le_mul' le_rfl (ghost_avoidance_upper h w S H hH hHm)
    _ = _ := by rw [← mul_assoc, sq]

end Percolation.BenjaminiSchramm

end

end OAI
