import Mathlib
import OAI.Probability.CriticalPercolation.Growth.PolynomialGrowthDescent

namespace OAI

section
noncomputable section
open Set Function Filter Topology
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A : Type*} [Group A] [DecidableEq A]

lemma eventually_exponential_dominates (C k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C*n^k < 2^n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1:ℝ)<2)).const_mul (C:ℝ)
  have he : ∀ᶠ n : ℕ in atTop, (C:ℝ)*((n:ℝ)^k / 2^n) < 1 :=
    ht.eventually (Iio_mem_nhds (by simp : (C:ℝ)*0 < 1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hx := hN n hn
  rw [← mul_div_assoc] at hx
  have hx' := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hx
  exact_mod_cast hx'

lemma not_quadratic_exponential_lower (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (L : ℕ) (hL : 0<L)
    (hlo : ∀ n : ℕ, 2^n ≤ (S^(L*n^2)).card) : False := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨N,hN⟩ := eventually_exponential_dominates (C*(4*L)^d) (2*d)
  obtain ⟨r,hr,hbound⟩ := hC (L*(max N 1)^2)
  let n := Nat.sqrt (r/L)
  have hn : max N 1 ≤ n := Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hL).mpr (by
    simpa only [Nat.mul_comm] using hr))
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnr : L*n^2 ≤ r := by
    calc
      _ ≤ L*(r/L) := Nat.mul_le_mul_left L (Nat.sqrt_le' (r/L))
      _ ≤ r := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self r L
  have hrn : r ≤ (4*L)*n^2 := by
    have ht := Nat.lt_mul_div_succ r hL
    have hs : r/L+1 ≤ (n+1)^2 := Nat.succ_le_of_lt (Nat.lt_succ_sqrt' (r/L))
    have hs' : (n+1)^2 ≤ 4*n^2 := by nlinarith
    have hj := (Nat.mul_le_mul_left L hs).trans (Nat.mul_le_mul_left L hs')
    nlinarith
  have hu : 2^n ≤ (C*(4*L)^d)*n^(2*d) := by
    calc
      _ ≤ (S^(L*n^2)).card := hlo n
      _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^d := hbound
      _ ≤ C*((4*L)*n^2)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
      _ = (C*(4*L)^d)*n^(2*d) := by rw [mul_pow,pow_mul]; ring
  exact (not_le_of_gt (hN n ((le_max_left N 1).trans hn))) hu

def binaryProducts (g : ℕ → A) : ℕ → Finset A
  | 0 => {1}
  | n+1 => binaryProducts g n ∪ (binaryProducts g n).image (fun x => g n*x)

lemma binaryProducts_mem (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) :
    ∀ n, ∀ x ∈ binaryProducts g n, x∈K n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have he : x=1 := by simpa [binaryProducts] using hx
    exact he ▸ (K 0).one_mem
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hK (Nat.le_succ n) (ih x hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (K (n+1)).mul_mem (hg n) (hK (Nat.le_succ n) (ih y hy))

lemma binaryProducts_card (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hg : ∀ n, g n∈K (n+1)) (hout : ∀ n, g n∉K n) :
    ∀ n, (binaryProducts g n).card=2^n := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    have hd : Disjoint (binaryProducts g n)
        ((binaryProducts g n).image (fun x => g n*x)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      have hxK := binaryProducts_mem K hK g hg n x hx
      have hyK := binaryProducts_mem K hK g hg n y hy
      apply hout n
      rw [←he] at hxK
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using
        (K n).mul_mem hxK ((K n).inv_mem hyK)
    rw [binaryProducts,Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ (mul_right_injective (g n)),ih,pow_succ]
    omega

lemma binaryProducts_subset_pow (S : Finset A) (h1 : (1:A)∈S)
    (g : ℕ → A) (L : ℕ) (hg : ∀ n, g n∈S^(L*(n+1))) :
    ∀ n, binaryProducts g n ⊆ S^(L*n^2) := by
  intro n
  induction n with
  | zero => simp [binaryProducts]
  | succ n ih =>
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L (Nat.pow_le_pow_left (Nat.le_succ n) 2)) (ih hx)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hlen : L*(n+1)+L*n^2 ≤ L*(n+1)^2 := by
        calc
          _ = L*(n+1+n^2) := by ring
          _ ≤ L*(n+1)^2 := Nat.mul_le_mul_left L (by nlinarith)
      apply Finset.pow_subset_pow_right h1 hlen
      rw [pow_add]
      exact Finset.mul_mem_mul (hg n) (ih hy)

theorem no_linear_word_strict_chain (S : Finset A) (h1 : (1:A)∈S)
    (d : ℕ) (hg : HasDegree S d) (K : ℕ → Subgroup A) (hK : Monotone K)
    (g : ℕ → A) (hgin : ∀ n, g n∈K (n+1)) (hgout : ∀ n, g n∉K n)
    (L : ℕ) (hL : 0<L) (hword : ∀ n, g n∈S^(L*(n+1))) : False := by
  apply not_quadratic_exponential_lower S h1 d hg L hL
  intro n
  rw [←binaryProducts_card K hK g hgin hgout n]
  exact Finset.card_le_card (binaryProducts_subset_pow S h1 g L hword n)

def boundedConjugates (S F : Finset A) (n : ℕ) : Finset A :=
  (S^n).biUnion (fun g => F.image (MulAut.conj g))

def conjugateStage (S F : Finset A) (n : ℕ) : Subgroup A :=
  Subgroup.closure (boundedConjugates S F n : Set A)

lemma mem_boundedConjugates (S F : Finset A) (n : ℕ) {x : A} :
    x∈boundedConjugates S F n ↔ ∃ g∈S^n, ∃ f∈F, g*f*g⁻¹=x := by
  simp [boundedConjugates, MulAut.conj_apply]

lemma boundedConjugates_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (boundedConjugates S F) := by
  intro m n h x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F m).mp hx
  exact (mem_boundedConjugates S F n).mpr
    ⟨g,Finset.pow_subset_pow_right h1 h hg,f,hf,rfl⟩

lemma conjugateStage_mono (S F : Finset A) (h1 : (1:A)∈S) :
    Monotone (conjugateStage S F) := by
  intro m n h
  exact Subgroup.closure_mono (boundedConjugates_mono S F h1 h)

lemma boundedConjugates_subset_pow (S F : Finset A) (hsym : S⁻¹=S)
    (L : ℕ) (hF : F⊆S^L) (n : ℕ) :
    boundedConjugates S F n ⊆ S^(2*n+L) := by
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  have hgi : g⁻¹∈S^n := by
    rw [←hsym,inv_pow]
    exact Finset.inv_mem_inv hg
  have he : 2*n+L=n+L+n := by omega
  rw [he,pow_add,pow_add]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul hg (hF hf)) hgi

lemma conjugateStage_le_normalClosure (S F : Finset A) (n : ℕ) :
    conjugateStage S F n ≤ Subgroup.normalClosure (F : Set A) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hx
  exact Subgroup.normalClosure_normal.conj_mem f (Subgroup.subset_normalClosure hf) g

lemma conjugateStage_conj_generator (S F : Finset A) (n : ℕ)
    (s : A) (hs : s∈S) {x : A} (hx : x∈conjugateStage S F n) :
    s*x*s⁻¹∈conjugateStage S F (n+1) := by
  change x∈Subgroup.closure _ at hx
  have hmap : conjugateStage S F n ≤
      (conjugateStage S F (n+1)).comap (MulAut.conj s) := by
    apply (Subgroup.closure_le _).mpr
    intro y hy
    obtain ⟨g,hg,f,hf,rfl⟩ := (mem_boundedConjugates S F n).mp hy
    apply Subgroup.subset_closure
    apply (mem_boundedConjugates S F (n+1)).mpr
    refine ⟨s*g,?_,f,hf,?_⟩
    · rw [pow_succ']
      exact Finset.mul_mem_mul hs hg
    · simp [MulAut.conj_apply,mul_assoc]
  exact hmap hx

lemma conjugateStage_normal_of_stationary (S F : Finset A) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (n : ℕ)
    (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    (conjugateStage S F n).Normal := by
  rw [←Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  change ∀ x, x∈conjugateStage S F n ↔ s*x*s⁻¹∈conjugateStage S F n
  intro x
  constructor
  · intro hx
    rw [←he]
    exact conjugateStage_conj_generator S F n s hs hx
  · intro hx
    have hsi : s⁻¹∈S := by rw [←hsym]; exact Finset.inv_mem_inv hs
    have hy := conjugateStage_conj_generator S F n s⁻¹ hsi hx
    rw [he] at hy
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using hy

lemma normalClosure_eq_conjugateStage_of_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (n : ℕ) (he : conjugateStage S F (n+1)=conjugateStage S F n) :
    Subgroup.normalClosure (F : Set A)=conjugateStage S F n := by
  let _ := conjugateStage_normal_of_stationary S F hsym hgen n he
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro f hf
    apply Subgroup.subset_closure
    exact (mem_boundedConjugates S F n).mpr
      ⟨1,Finset.one_mem_pow h1,f,hf,by simp⟩
  · exact conjugateStage_le_normalClosure S F n

theorem exists_conjugateStage_stationary (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (d : ℕ) (hg : HasDegree S d)
    (L : ℕ) (hF : F⊆S^L) :
    ∃ n : ℕ, conjugateStage S F (n+1)=conjugateStage S F n := by
  by_contra! hn
  have hw : ∀ n : ℕ, ∃ x∈boundedConjugates S F (n+1), x∉conjugateStage S F n := by
    intro n
    by_contra! h
    apply hn n
    apply le_antisymm ((Subgroup.closure_le _).mpr h)
    exact conjugateStage_mono S F h1 (Nat.le_succ n)
  choose g hgin hgout using hw
  apply no_linear_word_strict_chain S h1 d hg (conjugateStage S F)
    (conjugateStage_mono S F h1) g (fun n => Subgroup.subset_closure (hgin n))
    hgout (L+2) (by omega)
  intro n
  apply Finset.pow_subset_pow_right h1 (show 2*(n+1)+L≤(L+2)*(n+1) by nlinarith)
  exact boundedConjugates_subset_pow S F hsym L hF (n+1) (hgin n)

theorem normalClosure_fg_of_sparse_growth (S F : Finset A)
    (h1 : (1:A)∈S) (hsym : S⁻¹=S) (hgen : Subgroup.closure (S : Set A)=⊤)
    (d : ℕ) (hg : HasDegree S d) : (Subgroup.normalClosure (F : Set A)).FG := by
  obtain ⟨L,hF⟩ := finite_subset_word_ball S h1 hsym hgen F
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S F h1 hsym d hg L hF
  rw [normalClosure_eq_conjugateStage_of_stationary S F h1 hsym hgen n hn]
  exact (Subgroup.fg_iff _).mpr ⟨(boundedConjugates S F n : Set A),rfl,Finset.finite_toSet _⟩

end CriticalPercolation.SparseGrowth
end
end

end OAI
