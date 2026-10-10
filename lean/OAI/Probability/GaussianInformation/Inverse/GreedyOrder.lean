import Mathlib
import OAI.Probability.GaussianInformation.Inverse.GramVolume

namespace OAI
open MeasureTheory Metric
open scoped ENNReal
namespace AllScaleInverseVolume
open Set
open scoped Topology NNReal
open InnerProductSpace
open scoped RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def Greedy {α : Type*} {k : ℕ} (D : (Fin k → α) → Fin k → α → ℝ) (f : Fin k → α) : Prop :=
  ∀ i j : Fin k,i ≤ j → D f i (f j) ≤ D f i (f i)

lemma swap_preserves_lower_bound {k : ℕ} {b i j c : Fin k}
    (hij : i ≤ j) (hbi : b ≤ i) (hbc : b ≤ c) : b ≤ Equiv.swap i j c := by
  classical
  by_cases hci : c=i
  · subst c; simpa using hbi.trans hij
  by_cases hcj : c=j
  · subst c; simpa using hbi
  simpa [Equiv.swap_apply_of_ne_of_ne hci hcj] using hbc

lemma exists_greedy_permutation {α : Type*} {k : ℕ}
    (D : (Fin k → α) → Fin k → α → ℝ)
    (hD : ∀ f g i,(∀ j,i > j → f j=g j) → ∀ x,D f i x=D g i x)
    (f : Fin k → α) : ∃ π : Equiv.Perm (Fin k),Greedy D (f ∘ π) := by
  classical
  have build : ∀ m : ℕ,m ≤ k → ∃ π : Equiv.Perm (Fin k),
      ∀ i j : Fin k,i.val < m → i ≤ j → D (f ∘ π) i (f (π j)) ≤ D (f ∘ π) i (f (π i)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨Equiv.refl _,fun i j hi _ => (Nat.not_lt_zero _ hi).elim⟩
    | succ m ih =>
      intro hm
      obtain ⟨π,hπ⟩ := ih (by omega)
      let i : Fin k := ⟨m,by omega⟩
      obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.Ici i)
        (fun j : Fin k => D (f ∘ π) i (f (π j))) (by simp)
      have hij : i ≤ j := Finset.mem_Ici.mp hj
      let τ := Equiv.swap i j
      have hfix : ∀ a : Fin k,a < i → τ a=a := by
        intro a ha
        exact Equiv.swap_apply_of_ne_of_ne (ne_of_lt ha) (ne_of_lt (ha.trans_le hij))
      have hpref : ∀ b : Fin k,b ≤ i → ∀ a : Fin k,a < b →
          (f ∘ (τ.trans π)) a = (f ∘ π) a := by
        intro b hb a ha
        simp only [Function.comp_apply,Equiv.trans_apply,hfix a (ha.trans_le hb)]
      refine ⟨τ.trans π,?_⟩
      intro b c hb hbc
      have hbi : b ≤ i := by change b.val ≤ m; omega
      have hscore := hD (f ∘ (τ.trans π)) (f ∘ π) b (hpref b hbi)
      by_cases hbeq : b=i
      · subst b
        simp only [Equiv.trans_apply] at hscore ⊢
        rw [hscore,hscore]
        have hτi : τ i=j := Equiv.swap_apply_left i j
        rw [hτi]
        exact hmax (τ c) (Finset.mem_Ici.mpr (swap_preserves_lower_bound hij le_rfl hbc))
      · have hblt : b < i := lt_of_le_of_ne hbi hbeq
        simp only [Equiv.trans_apply] at hscore ⊢
        rw [hscore,hscore,hfix b hblt]
        exact hπ b (τ c) (by change b.val < m at hblt; exact hblt)
          (swap_preserves_lower_bound hij hbi hbc)
  obtain ⟨π,hπ⟩ := build k le_rfl
  exact ⟨π,fun i j hij => hπ i j i.isLt hij⟩
noncomputable def prefixResidual {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k)
    (x : Ambient d) : Ambient d := orthoResidual (gramSchmidtNormed ℝ f) (Finset.Iio i) x
noncomputable def prefixAxes {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) : Fin k → Ambient d :=
  fun j => if j < i then gramSchmidtNormed ℝ f j else 0

lemma prefixAxes_suborthonormal {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) :
    Suborthonormal (prefixAxes f i) :=
  (gramSchmidtNormed_suborthonormal f).cut (Set.Iio i)

lemma gramSchmidtNormed_term {d k : ℕ} (f : Fin k → Ambient d) (j : Fin k) (x : Ambient d) :
    (inner ℝ (gramSchmidtNormed ℝ f j) x) • gramSchmidtNormed ℝ f j =
      (inner ℝ (gramSchmidt ℝ f j) x / ‖gramSchmidt ℝ f j‖^2) • gramSchmidt ℝ f j := by
  simp only [gramSchmidtNormed,real_inner_smul_left,smul_smul]
  congr 1
  simp only [div_eq_mul_inv,RCLike.ofReal_real_eq_id,id_eq]
  ring

lemma prefixResidual_self {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) :
    prefixResidual f i (f i)=gramSchmidt ℝ f i := by
  calc
    _ = f i-∑ j ∈ Finset.Iio i,(inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖^2) • gramSchmidt ℝ f j := by
      simp only [prefixResidual,orthoResidual,gramSchmidtNormed_term]
    _ = _ := (gramSchmidt_real_def f i).symm

lemma prefixResidual_eq {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) (x : Ambient d) :
    residual (prefixAxes f i) x=prefixResidual f i x := by
  classical
  have hI : Finset.univ.filter (fun j : Fin k => j < i)=Finset.Iio i := by ext j; simp
  simp only [residual,synth,coordinates,prefixAxes,prefixResidual,orthoResidual,WithLp.ofLp_toLp]
  congr 1
  calc
    _ = ∑ j : Fin k,if j < i then (inner ℝ (gramSchmidtNormed ℝ f j) x) • gramSchmidtNormed ℝ f j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < i <;> simp [hj]
    _ = _ := by rw [← Finset.sum_filter,hI]

lemma prefixResidual_prefix_congr {d k : ℕ} {f g : Fin k → Ambient d} (i : Fin k)
    (hfg : ∀ j,j < i → f j=g j) (x : Ambient d) : prefixResidual f i x=prefixResidual g i x := by
  unfold prefixResidual orthoResidual
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have he : gramSchmidtNormed ℝ f j=gramSchmidtNormed ℝ g j := by
    simp only [gramSchmidtNormed,gramSchmidt_prefix_congr j
      (fun a ha => hfg a (ha.trans_lt (Finset.mem_Iio.mp hj)))]
  rw [he]

lemma prefixAxes_prefix_congr {d k : ℕ} {f g : Fin k → Ambient d} (i : Fin k)
    (hfg : ∀ j,j < i → f j=g j) : prefixAxes f i=prefixAxes g i := by
  funext j
  by_cases hj : j < i
  · simp only [prefixAxes,ite_eq_left hj,gramSchmidtNormed,gramSchmidt_prefix_congr j
      (fun a ha => hfg a (ha.trans_lt hj))]
  · simp [prefixAxes,hj]

lemma measurable_gramSchmidtNormed {d k : ℕ} (j : Fin k) :
    Measurable (fun f : Fin k → Ambient d => gramSchmidtNormed ℝ f j) :=
  (measurable_gramSchmidt j).norm.inv.smul (measurable_gramSchmidt j)

lemma measurable_prefixAxes {d k : ℕ} (i j : Fin k) :
    Measurable (fun f : Fin k → Ambient d => prefixAxes f i j) := by
  by_cases hj : j < i
  · simpa [prefixAxes,hj] using measurable_gramSchmidtNormed (d := d) j
  · simp [prefixAxes,hj]

lemma measurable_prefixResidual {d k : ℕ} (i : Fin k) :
    Measurable (fun p : (Fin k → Ambient d) × Ambient d => prefixResidual p.1 i p.2) := by
  unfold prefixResidual orthoResidual
  apply measurable_snd.sub
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_gramSchmidtNormed (d := d) j).comp measurable_fst).inner (𝕜 := ℝ) measurable_snd).smul
    ((measurable_gramSchmidtNormed (d := d) j).comp measurable_fst)

noncomputable def residualScore {d k : ℕ} (f : Fin k → Ambient d) (i : Fin k) (x : Ambient d) : ℝ :=
  ‖prefixResidual f i x‖

lemma exists_greedy_gram_order {d k : ℕ} (f : Fin k → Ambient d) :
    ∃ π : Equiv.Perm (Fin k),Greedy residualScore (f ∘ π) := by
  apply exists_greedy_permutation
  intro f g i hfg x
  exact congrArg norm (prefixResidual_prefix_congr i hfg x)

lemma greedy_lengths_antitone {d k : ℕ} {f : Fin k → Ambient d}
    (hg : Greedy residualScore f) : Antitone (fun i => ‖gramSchmidt ℝ f i‖) := by
  intro i j hij
  calc
    _ = ‖prefixResidual f j (f j)‖ := by rw [prefixResidual_self]
    _ ≤ ‖prefixResidual f i (f j)‖ :=
      orthoResidual_norm_antitone (gramSchmidtNormed_suborthonormal f) (Finset.Iio_subset_Iio hij) _
    _ ≤ ‖prefixResidual f i (f i)‖ := hg i j hij
    _ = _ := by rw [prefixResidual_self]

lemma measurableSet_greedy {d k : ℕ} : MeasurableSet {f : Fin k → Ambient d | Greedy residualScore f} := by
  simp only [Greedy,residualScore,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le
    ((measurable_prefixResidual i).comp (measurable_id.prodMk (measurable_pi_apply j))).norm
    ((measurable_prefixResidual i).comp (measurable_id.prodMk (measurable_pi_apply i))).norm

end AllScaleInverseVolume

end OAI
