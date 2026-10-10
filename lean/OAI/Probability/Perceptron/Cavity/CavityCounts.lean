import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkCompactGG

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityOmittedCount (α : ℝ) (n : ℕ) : ℕ := patternCount α (n+1)-2

def cavityFreshCount (α : ℝ) (n L : ℕ) : ℕ := patternCount α (n+1+L)-patternCount α (n+1)

lemma cavity_count_bounds {α : ℝ} (hα : 0≤α) (N : ℕ) :
    α*N-1≤(patternCount α N:ℝ) ∧ (patternCount α N:ℝ)≤α*N := by
  constructor
  · have h:=Nat.lt_floor_add_one (α*(N:ℝ))
    dsimp only [patternCount]
    linarith
  · exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg N))

lemma cavity_count_density {α : ℝ} (hα : 0≤α) :
    Tendsto (fun n=>(patternCount α (n+1):ℝ)/(n+1:ℕ)) atTop (𝓝 α) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi:=tendsto_inv_atTop_zero.comp hN
  have hl: Tendsto (fun n : ℕ=>α-((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 α) := by
    simpa only [sub_zero,Function.comp_def] using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    have h:=(cavity_count_bounds hα (n+1)).1
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
    calc
      _ = α*(n+1:ℕ)-1 := by field_simp
      _ ≤ _ := h
  · intro n
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr (cavity_count_bounds hα (n+1)).2

lemma cavity_count_eventually_two {α : ℝ} (hα : 0<α) :
    ∀ᶠ n : ℕ in atTop,2≤patternCount α (n+1) := by
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h:= (hN.const_mul_atTop hα).eventually_ge_atTop 3
  filter_upwards [h] with n hn
  have hb:=(cavity_count_bounds hα.le (n+1)).1
  have hc : (2:ℝ)≤patternCount α (n+1) := by linarith
  exact_mod_cast hc

lemma cavity_omitted_full {α : ℝ} (hα : 0<α) :
    ∀ᶠ n : ℕ in atTop,cavityOmittedCount α n+2=patternCount α (n+1) := by
  filter_upwards [cavity_count_eventually_two hα] with n hn
  exact Nat.sub_add_cancel hn

lemma cavity_omitted_density {α : ℝ} (hα : 0<α) :
    Tendsto (fun n=>((cavityOmittedCount α n+2:ℕ):ℝ)/(n+1:ℕ)) atTop (𝓝 α) := by
  apply (cavity_count_density hα.le).congr'
  filter_upwards [cavity_omitted_full hα] with n hn
  rw [hn]

lemma cavity_omitted_bound {α : ℝ} (hα : 0≤α) (n : ℕ) :
    ((cavityOmittedCount α n+2:ℕ):ℝ)/(n+1:ℕ)≤α+2 := by
  have h: ((cavityOmittedCount α n+2:ℕ):ℝ)≤(patternCount α (n+1):ℝ)+2 := by
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ 2) 2
  have hb:=(cavity_count_bounds hα (n+1)).2
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
  have hN : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith

lemma cavity_fresh_count {α : ℝ} (hα : 0≤α) (n L : ℕ) :
    patternCount α (n+1)+cavityFreshCount α n L=patternCount α (n+1+L) ∧
    |(cavityFreshCount α n L:ℝ)-(L:ℝ)*α|≤1 ∧
    cavityFreshCount α n L≤⌈(L:ℝ)*α+1⌉₊ := by
  have hm : patternCount α (n+1)≤patternCount α (n+1+L) :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right (n+1) L) hα)
  have he : (cavityFreshCount α n L:ℝ)=(patternCount α (n+1+L):ℝ)-(patternCount α (n+1):ℝ) := by
    exact Nat.cast_sub hm
  refine ⟨Nat.add_sub_of_le hm,?_,?_⟩
  · rw [he,abs_le]
    have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    constructor <;> nlinarith [h0.1,h0.2,h1.1,h1.2]
  · have h0:=cavity_count_bounds hα (n+1)
    have h1:=cavity_count_bounds hα (n+1+L)
    push_cast at h0 h1
    have hh : (cavityFreshCount α n L:ℝ)≤(L:ℝ)*α+1 := by rw [he]; nlinarith [h0.1,h1.2]
    exact_mod_cast hh.trans (Nat.le_ceil ((L:ℝ)*α+1))


structure CavityGoodParameters (α : ℝ) (f : ℝ→ᵇℝ) where
  J : ℕ→ℕ
  monotone : Monotone J
  le : ∀ n,J n≤n
  tendsto : Tendsto J atTop atTop
  measurable : ∀ n,MeasurableSet (bulkJointGoodSet α f J n)
  mass : Tendsto (fun n=>bulkParameterLaw.real (bulkJointGoodSet α f J n)ᶜ) atTop (𝓝 0)
  deviation : ∀ v : ℕ→ℕ→ℝ,(∀ᶠ n in atTop,v n∈bulkJointGoodSet α f J n)→
    ∀ p,Tendsto (fun n=>bulkDeviationAt n (patternCount α (n+1)) f p (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n=>omittedBulkDeviation α f n p (v n)) atTop (𝓝 0)

lemma exists_cavityGoodParameters {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) :
    Nonempty (CavityGoodParameters α f) := by
  obtain ⟨J,hm,hl,ht,hms,hma,hd⟩:=exists_bulkJointGoodParameters hα f
  exact ⟨⟨J,hm,hl,ht,hms,hma,hd⟩⟩

lemma CavityGoodParameters.nonempty {α : ℝ} {f : ℝ→ᵇℝ} (G : CavityGoodParameters α f) :
    ∀ᶠ n in atTop,(bulkJointGoodSet α f G.J n).Nonempty := by
  filter_upwards [G.mass.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  by_contra h
  have he : bulkJointGoodSet α f G.J n=∅:=Set.not_nonempty_iff_eq_empty.mp h
  simp only [he,compl_empty,probReal_univ] at hn
  exact lt_irrefl _ hn

lemma cavity_eventually_uniform {X : Type*} (S : ℕ→Set X) (T : Set X) (x0 : X)
    (hx0 : x0∈T) (hST : ∀ n,S n⊆T) (hS : ∀ᶠ n in atTop,(S n).Nonempty)
    (R : ℕ→X→Prop)
    (hR : ∀ v : ℕ→X,(∀ n,v n∈T)→(∀ᶠ n in atTop,v n∈S n)→∀ᶠ n in atTop,R n (v n)) :
    ∀ᶠ n in atTop,∀ x∈S n,R n x := by
  classical
  let v : ℕ→X:=fun n=>if h : ∃ x∈S n,¬R n x then h.choose
    else if h' : (S n).Nonempty then h'.choose else x0
  have hvT : ∀ n,v n∈T := by
    intro n
    dsimp only [v]
    split_ifs with h h'
    · exact hST n h.choose_spec.1
    · exact hST n h'.choose_spec
    · exact hx0
  have hvS : ∀ᶠ n in atTop,v n∈S n := by
    filter_upwards [hS] with n hn
    by_cases h : ∃ x∈S n,¬R n x
    · simpa only [v,dite_eq_left h] using h.choose_spec.1
    · simpa only [v,dite_eq_right h,dite_eq_left hn] using hn.choose_spec
  filter_upwards [hR v hvT hvS] with n hn
  intro x hx
  by_contra hbad
  have he : ∃ x∈S n,¬R n x:=⟨x,hx,hbad⟩
  have hneg : ¬R n (v n) := by
    dsimp only [v]
    rw [dite_eq_left he]
    exact he.choose_spec.2
  exact hneg hn
end SphericalPerceptronFreeEnergy

end

end OAI
