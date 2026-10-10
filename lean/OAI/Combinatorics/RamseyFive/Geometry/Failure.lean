import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Law

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β : Type*} [Fintype α] [Fintype β]

noncomputable def failure (p : Law α) (v : α → V) (f : Module.Dual K V) : ℝ :=
  ∑ a,if f (v a)≠0 then p a else 0

lemma failure_nonneg (p : Law α) (v : α → V) (f : Module.Dual K V) : 0≤failure p v f := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact p.nonneg a
  · exact le_rfl

noncomputable def core (p : Law α) (v : α → V) (ρ : ℝ) : Submodule K V :=
  ⨅ f : {f : Module.Dual K V // failure p v f≤ρ},LinearMap.ker f.val

lemma mem_core (p : Law α) (v : α → V) (ρ : ℝ) (x : V) :
    x∈core (K := K) p v ρ ↔ ∀ f : Module.Dual K V,failure p v f≤ρ → f x=0 := by
  simp only [core,Submodule.mem_iInf,LinearMap.mem_ker]
  exact ⟨fun h f hf => h ⟨f,hf⟩,fun h f => h f.val f.property⟩

lemma core_test (p : Law α) (v : α → V) (ρ : ℝ) (f : Module.Dual K V)
    (hf : failure p v f≤ρ) : core (K := K) p v ρ≤LinearMap.ker f := by
  intro x hx
  exact (mem_core (K := K) p v ρ x).mp hx f hf

theorem core_failure [FiniteDimensional K V] (p : Law α) (v : α → V) (ρ : ℝ) (hρ : 0≤ρ) :
    (∑ a,if v a∉core (K := K) p v ρ then p a else 0)≤finrank K V*ρ := by
  let S : Set (Module.Dual K V) := {f | failure p v f≤ρ}
  obtain ⟨T,hTS,hcard,hspan,_⟩ := Submodule.exists_finset_span_eq_linearIndepOn K S
  have hT : T.card≤finrank K V := by
    rw [hcard]
    exact (Submodule.finrank_le (Submodule.span K S)).trans_eq Subspace.dual_finrank_eq
  have hex (x : V) (hx : x∉core (K := K) p v ρ) : ∃ f∈T,f x≠0 := by
    by_contra hn
    have hz : ∀ f∈T,f x=0 := by simpa only [not_exists,not_and,not_not] using hn
    have hle : Submodule.span K (T:Set (Module.Dual K V))≤LinearMap.ker (Module.Dual.eval K V x) := by
      apply Submodule.span_le.mpr
      intro f hf
      exact hz f hf
    rw [hspan] at hle
    apply hx
    apply (mem_core (K := K) p v ρ x).mpr
    intro f hf
    exact hle (Submodule.subset_span (show f∈S from hf))
  have hpoint (a : α) :
      (if v a∉core (K := K) p v ρ then p a else 0)≤∑ f∈T,if f (v a)≠0 then p a else 0 := by
    by_cases h : v a∈core (K := K) p v ρ
    · simp only [h,not_true_eq_false,ite_false]
      exact Finset.sum_nonneg fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl
    · obtain ⟨f,hf,hfa⟩ := hex (v a) h
      simp only [h,not_false_eq_true,ite_true]
      have hh := Finset.single_le_sum (s := T) (f := fun f => if f (v a)≠0 then p a else 0)
        (fun _ _ => by split_ifs; exact p.nonneg a; exact le_rfl) hf
      simpa only [ite_eq_left hfa] using hh
  calc
    _ ≤ ∑ a,∑ f∈T,if f (v a)≠0 then p a else 0 := Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ f∈T,failure p v f := by rw [Finset.sum_comm]; rfl
    _ ≤ ∑ _f∈T,ρ := Finset.sum_le_sum fun f hf => hTS hf
    _ = (T.card:ℝ)*ρ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hT) hρ

theorem core_orthogonal (p : Law α) (v : α → Module.Dual K V)
    (q : Law β) (w : β → V) (ρ : ℝ) (hρ : 0<ρ)
    (hmiss : (∑ b,q b*failure p v (Module.Dual.eval K V (w b)))≤ρ^2)
    (x : Module.Dual K V) (hx : x∈core (K := K) p v ρ)
    (y : V) (hy : y∈core (K := K) q w ρ) : x y=0 := by
  let B := Finset.univ.filter fun b => ρ<failure p v (Module.Dual.eval K V (w b))
  have hmass : ρ*(∑ b∈B,q b)≤ρ^2 := by
    calc
      _ ≤ ∑ b∈B,q b*failure p v (Module.Dual.eval K V (w b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro b hb
        have hh := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hb).2.le (q.nonneg b)
        simpa only [mul_comm ρ] using hh
      _ ≤ ∑ b,q b*failure p v (Module.Dual.eval K V (w b)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => mul_nonneg (q.nonneg b) (failure_nonneg p v _))
      _ ≤ _ := hmiss
  have hB : (∑ b∈B,q b)≤ρ := by nlinarith
  have hf : failure q w x≤ρ := by
    apply le_trans _ hB
    rw [failure]
    have hh : (∑ b∈B,q b)=(∑ b,if b∈B then q b else 0) := by
      rw [←Finset.sum_filter]
      simp only [Finset.filter_univ_mem]
    rw [hh]
    apply Finset.sum_le_sum
    intro b _
    by_cases h : x (w b)=0
    · simp only [h,ne_eq,not_true_eq_false,ite_false]
      split_ifs; exact q.nonneg b; exact le_rfl
    · have hb : b∈B := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        by_contra hn
        have he := (mem_core (K := K) p v ρ x).mp hx (Module.Dual.eval K V (w b)) (le_of_not_gt hn)
        exact h he
      simp only [h,ne_eq,not_false_eq_true,ite_true,hb,le_refl]
  exact (mem_core (K := K) q w ρ y).mp hy x hf

noncomputable def capture (p : Law α) (v : α → V) (ρ : ℝ) : ℝ :=
  ∑ a,if v a∈core (K := K) p v ρ then p a else 0

lemma capture_zero_one (p : Law α) (v : α → V) (ρ : ℝ) :
    0≤capture (K := K) p v ρ ∧ capture (K := K) p v ρ≤1 := by
  constructor
  · apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact p.nonneg a
    · exact le_rfl
  · calc
      _ ≤ ∑ a,p a := Finset.sum_le_sum fun a _ => by
        split_ifs
        · exact le_rfl
        · exact p.nonneg a
      _ = 1 := p.sum_one

lemma capture_failure (p : Law α) (v : α → V) (ρ : ℝ) :
    capture (K := K) p v ρ+(∑ a,if v a∉core (K := K) p v ρ then p a else 0)=1 := by
  rw [capture,←Finset.sum_add_distrib]
  convert p.sum_one using 1
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

 theorem capture_lower [FiniteDimensional K V] (p : Law α) (v : α → V) (ρ : ℝ) (hρ : 0≤ρ) :
    1-(finrank K V:ℝ)*ρ≤capture (K := K) p v ρ := by
  linarith [capture_failure (K := K) p v ρ,core_failure (K := K) p v ρ hρ]

theorem product_core_capture [FiniteDimensional K V]
    (p : Law α) (q : Law β) (v : α → Module.Dual K V) (w : β → V)
    (ρ : ℝ) (hρ : 0≤ρ) :
    1-2*(finrank K V:ℝ)*ρ≤
      ∑ a,∑ b,if v a∈core (K := K) p v ρ ∧ w b∈core (K := K) q w ρ
        then p a*q b else 0 := by
  have he : (∑ a,∑ b,if v a∈core (K := K) p v ρ ∧ w b∈core (K := K) q w ρ
        then p a*q b else 0)=capture (K := K) p v ρ*capture (K := K) q w ρ := by
    rw [capture,capture,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp_all
  rw [he]
  have hp := capture_lower (K := K) p v ρ hρ
  have hq := capture_lower (K := K) q w ρ hρ
  rw [Subspace.dual_finrank_eq] at hp
  have hp1 := (capture_zero_one (K := K) p v ρ).2
  have hq1 := (capture_zero_one (K := K) q w ρ).2
  have hprod := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
  nlinarith

lemma source_core_capture [FiniteDimensional K V] (hdim : finrank K V=5)
    (p : Law α) (q : Law β) (v : α → Module.Dual K V) (w : β → V) :
    (19/20:ℝ)≤∑ a,∑ b,
      if v a∈core (K := K) p v (1/200) ∧ w b∈core (K := K) q w (1/200)
      then p a*q b else 0 := by
  have h := product_core_capture p q v w (1/200) (by norm_num)
  norm_num [hdim] at h
  exact h
end SharpRamseyFive.CoreGeometry

end OAI
