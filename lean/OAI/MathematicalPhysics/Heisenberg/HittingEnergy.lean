import OAI.MathematicalPhysics.Heisenberg.HittingKernels

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical

open scoped Classical
open Filter
namespace Heisenberg.Hitting

variable {V : Type*} [Fintype V]

structure DoublySubstochastic (U : Matrix V V ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ U i j
  row : ∀ i, ∑ j, U i j ≤ 1
  col : ∀ j, ∑ i, U i j ≤ 1

def backward (U : Matrix V V ℝ) (f : V → ℝ) (i : V) : ℝ := ∑ j, U j i * f j

def hitStep (U : Matrix V V ℝ) (T : Finset V) (f : V → ℝ) (i : V) : ℝ :=
  if i ∈ T then 1 else backward U f i

def hitIter (U : Matrix V V ℝ) (T : Finset V) : ℕ → V → ℝ
  | 0 => fun i => if i ∈ T then 1 else 0
  | n + 1 => hitStep U T (hitIter U T n)

lemma backward_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f g : V → ℝ} (hfg : f ≤ g) : backward U f ≤ backward U g := by
  intro i
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hfg j) (hU.nonneg j i)

lemma backward_nonneg {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f : V → ℝ} (hf : 0 ≤ f) : 0 ≤ backward U f := by
  intro i
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hU.nonneg j i) (hf j))

lemma backward_le_one {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    {f : V → ℝ} (hf : f ≤ 1) : backward U f ≤ 1 := by
  intro i
  exact (Finset.sum_le_sum (fun j _ =>
    mul_le_of_le_one_right (hU.nonneg j i) (hf j))).trans (hU.col i)

lemma hitStep_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : Monotone (hitStep U T) := by
  intro f g h i
  dsimp [hitStep]
  split_ifs
  · rfl
  · exact backward_mono hU h i

lemma hitIter_bounds {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (n : ℕ) : 0 ≤ hitIter U T n ∧ hitIter U T n ≤ 1 := by
  induction n with
  | zero => constructor <;> intro i <;> simp [hitIter] <;> split_ifs <;> norm_num
  | succ n ih =>
    constructor <;> intro i <;> dsimp [hitIter, hitStep] <;> split_ifs
    · norm_num
    · exact backward_nonneg hU ih.1 i
    · rfl
    · exact backward_le_one hU ih.2 i

lemma hitIter_mono {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : Monotone (hitIter U T) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro i
    dsimp [hitIter, hitStep]
    split_ifs
    · rfl
    · exact backward_nonneg hU (hitIter_bounds hU T 0).1 i
  | succ n ih => exact hitStep_mono hU T ih

def hitting (U : Matrix V V ℝ) (T : Finset V) (i : V) : ℝ :=
  ⨆ n, hitIter U T n i

lemma hitIter_bdd {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (i : V) : BddAbove (Set.range (fun n => hitIter U T n i)) :=
  ⟨1, fun _ ⟨n, hn⟩ => hn ▸ (hitIter_bounds hU T n).2 i⟩

lemma hitIter_tendsto {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) (i : V) :
    Tendsto (fun n => hitIter U T n i) atTop (nhds (hitting U T i)) :=
  tendsto_atTop_ciSup (fun _ _ h => hitIter_mono hU T h i) (hitIter_bdd hU T i)

lemma hitting_bounds {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) : 0 ≤ hitting U T ∧ hitting U T ≤ 1 := by
  constructor
  · intro i
    exact (hitIter_bounds hU T 0).1 i |>.trans (le_ciSup (hitIter_bdd hU T i) 0)
  · intro i
    exact ciSup_le (fun n => (hitIter_bounds hU T n).2 i)

lemma hitting_on {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∈ T) : hitting U T i = 1 := by
  apply le_antisymm ((hitting_bounds hU T).2 i)
  have h := le_ciSup (hitIter_bdd hU T i) 0
  simpa only [hitIter, ite_eq_left hi, Pi.one_apply, hitting] using h

lemma hitting_harmonic {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∉ T) :
    backward U (hitting U T) i = hitting U T i := by
  have ha : Tendsto (fun n => backward U (hitIter U T n) i) atTop
      (nhds (backward U (hitting U T) i)) := by
    unfold backward
    exact tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (hitIter_tendsto hU T j))
  have hb : Tendsto (fun n => backward U (hitIter U T n) i) atTop
      (nhds (hitting U T i)) := by
    have ht := (hitIter_tendsto hU T i).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n => hitIter U T (n + 1) i) atTop _ at ht
    simpa only [hitIter, hitStep, ite_eq_right hi] using ht
  exact tendsto_nhds_unique ha hb

theorem hitting_minimal {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {g : V → ℝ} (hg : 0 ≤ g)
    (hgT : ∀ i ∈ T, g i = 1) (hgh : ∀ i ∉ T, backward U g i = g i) :
    hitting U T ≤ g := by
  have hn (n : ℕ) : hitIter U T n ≤ g := by
    induction n with
    | zero => intro i; dsimp [hitIter]; split_ifs with hi
              · rw [hgT i hi]
              · exact hg i
    | succ n ih =>
      intro i
      dsimp [hitIter, hitStep]
      split_ifs with hi
      · rw [hgT i hi]
      · exact (backward_mono hU ih i).trans_eq (hgh i hi)
  exact fun i => ciSup_le (fun n => hn n i)

def energy (U : Matrix V V ℝ) (f : V → ℝ) : ℝ :=
  ∑ i, f i * (f i - ∑ j, U i j * f j)

lemma energy_transpose (U : Matrix V V ℝ) (f : V → ℝ) :
    energy U f = ∑ i, f i * (f i - backward U f i) := by
  simp only [energy, backward, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hitting_energy {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) :
    energy U (hitting U T) = ∑ i ∈ T, (1 - backward U (hitting U T) i) := by
  rw [energy_transpose]
  rw [← Finset.sum_subset (Finset.subset_univ T)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hitting_on hU T hi, one_mul]
  · intro i _ hi
    rw [hitting_harmonic hU T hi, sub_self, mul_zero]

end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Matrix Heisenberg.Hitting
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def killedMean (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V) : Matrix V V ℝ :=
  fun i j => if i∈D ∧ j∈D then ∑ c,μ c*(if i=σ c j then 1 else 0) else 0

lemma killedMean_substochastic (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (D : Set V) : DoublySubstochastic (killedMean μ σ D) := by
  have hn : ∀ i j,0≤killedMean μ σ D i j := by
    intro i j
    unfold killedMean
    split_ifs
    · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
    · rfl
  constructor
  · exact hn
  · intro i
    calc
      _ ≤ ∑ j,∑ c,μ c*(if i=σ c j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        unfold killedMean
        split_ifs
        · rfl
        · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
      _ = 1 := by
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum]
        have he (c) : (∑ j : V,if i=σ c j then (1:ℝ) else 0)=1 := by
          convert Finset.sum_ite_eq' Finset.univ ((σ c).symm i) (fun _ => (1:ℝ)) using 1
          · apply Finset.sum_congr rfl
            intro j _
            congr 1
            exact propext (by rw [Equiv.eq_symm_apply,eq_comm])
          · simp
        simp only [he,mul_one,hs]
  · intro j
    calc
      _ ≤ ∑ i,∑ c,μ c*(if i=σ c j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        unfold killedMean
        split_ifs
        · rfl
        · exact Finset.sum_nonneg (fun c _ => mul_nonneg (hμ c) (by split_ifs <;> norm_num))
      _ = 1 := by
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum]
        simpa using hs

lemma killedMean_backward (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V)
    (f : V → ℝ) (hf : ∀ x,x∉D → f x=0) (i : V) (hi : i∈D) :
    backward (killedMean μ σ D) f i = ∑ c,μ c*f (σ c i) := by
  unfold backward killedMean
  have he : ∀ j,(if j∈D ∧ i∈D then ∑ c,μ c*(if j=σ c i then 1 else 0) else 0)*f j =
      ∑ c,μ c*(if j=σ c i then f j else 0) := by
    intro j
    by_cases hj : j∈D
    · simp only [hj,hi,and_self,ite_true,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    · simp [hj,hf j hj]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

lemma killed_hitting_supported (μ : Ω → ℝ) (σ : Ω → Equiv.Perm V) (D : Set V)
    (hK : DoublySubstochastic (killedMean μ σ D)) (T : Finset V)
    (hT : (T:Set V) ⊆ D) (x : V) (hx : x∉D) : hitting (killedMean μ σ D) T x=0 := by
  have ht : x∉T := fun h => hx (hT h)
  rw [←hitting_harmonic hK T ht]
  simp [backward,killedMean,hx]

theorem split_conditional_return_energy (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (A P D : Set V)
    (hA : ∀ c x,σ c x∉A ↔ x∉A)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))≠0)
    (T : Finset {x : {z : V // z∉A} // x.val∈P})
    (hT : ∀ j∈T,j.val.val∈D) (hQ : Aᶜ∩Pᶜ ⊆ D) :
    let U := killedMean μ σ D
    let T' := T.image (fun j => j.val.val)
    (∑ c,if hw : AllHit (splitHolePerm (σ c) A P (hA c)) then
      (μ c / hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c))) *
        (∑ j∈T,if nextPin (splitHolePerm (σ c) A P (hA c)) hw j∈T then (1:ℝ) else 0) else 0) ≤
      (T.card:ℝ)-energy U (hitting U T') := by
  dsimp only
  let T' := T.image (fun j => j.val.val)
  let U := killedMean μ σ D
  have hU := killedMean_substochastic μ hμ hs σ D
  let f := hitting U T'
  have hTD : (T':Set V) ⊆ D := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact hT j hj
  have hf : ∀ x,x∉D → f x=0 := killed_hitting_supported μ σ D hU T' hTD
  have hb := split_conditional_return_le μ hμ σ A P hA hd hz T f (hitting_bounds hU T').1
    (fun j hj => by
      change 1 ≤ hitting U T' j.val.val
      exact le_of_eq (hitting_on hU T' (Finset.mem_image.mpr ⟨j,hj,rfl⟩)).symm)
    (by
      intro x hxA hxP
      rw [mean_perm_backward,←killedMean_backward μ σ D f hf x (hQ ⟨hxA,hxP⟩)]
      have hxT : x∉T' := by
        intro hx
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
        exact hxP j.property
      exact le_of_eq (hitting_harmonic hU T' hxT))
  have hinj : Function.Injective (fun j : {x : {z : V // z∉A} // x.val∈P} => j.val.val) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have he : energy U f = (T.card:ℝ)-∑ j∈T,backward U f j.val.val := by
    rw [hitting_energy hU T',Finset.sum_sub_distrib]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,T',Finset.card_image_of_injective _ hinj]
    rw [Finset.sum_image (by intro a _ b _ h; exact hinj h)]
  rw [he]
  have he' : (∑ j∈T,((∑ c,μ c • (σ c).permMatrix ℝ)*ᵥ f) j.val.val) =
      ∑ j∈T,backward U f j.val.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mean_perm_backward,killedMean_backward μ σ D f hf _ (hT j hj)]
  rw [he'] at hb
  linarith

end Heisenberg.Exposure
end

end OAI
