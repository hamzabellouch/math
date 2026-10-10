import Mathlib

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter
open scoped Topology

/-- A purely numerical telescope, used on the averaged pressure at sizes n+1. -/
lemma extensive_lower_bound {P : ℕ → ℝ} {v : ℝ} {n : ℕ}
    (h : ∀ N, n ≤ N → v ≤ P (N+1)-P N) :
    ∀ N, n ≤ N → P n+((N:ℝ)-n)*v ≤ P N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hs := h N hN
    push_cast
    nlinarith

/-- Infinitely many low increments follow from the physical liminf and a
vanishing normalized perturbation. No low-increment sequence is assumed. -/
theorem arbitrarily_large_low_increment (P f : ℕ → ℝ)
    (hbelow : atTop.IsBoundedUnder (· ≥ ·) f)
    (habove : atTop.IsCoboundedUnder (· ≥ ·) f)
    (hnear : Tendsto (fun N => P N/((N:ℝ)+1)-f N) atTop (𝓝 0))
    {v : ℝ} (hv : liminf f atTop < v) (n : ℕ) :
    ∃ N, n ≤ N ∧ P (N+1)-P N ≤ v := by
  by_contra hn
  push Not at hn
  have hlin := extensive_lower_bound (fun N hN => (hn N hN).le)
  let a := (liminf f atTop+v)/2
  have hfa : liminf f atTop < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have htconst : Tendsto (fun N : ℕ => (P n-v*((n:ℝ)+1))/((N:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (P n-v*((n:ℝ)+1))
  have ht : Tendsto (fun N : ℕ => v+(P n-v*((n:ℝ)+1))/((N:ℝ)+1)-
      (P N/((N:ℝ)+1)-f N)) atTop (𝓝 v) := by
    simpa using (tendsto_const_nhds.add htconst).sub hnear
  have hlo : ∀ᶠ N in atTop, a < f N := by
    filter_upwards [ht.eventually (lt_mem_nhds hav),eventually_ge_atTop n] with N ha hN
    have hd : (0:ℝ) < (N:ℝ)+1 := by positivity
    have hb := (div_le_div_of_nonneg_right (hlin N hN) hd.le)
    have he : (P n+((N:ℝ)-n)*v)/((N:ℝ)+1) =
        v+(P n-v*((n:ℝ)+1))/((N:ℝ)+1) := by field_simp; ring
    rw [he] at hb
    linarith
  exact (not_le_of_gt hfa) ((le_liminf_iff habove hbelow).2 fun threshold hthreshold =>
    hlo.mono fun size hsize => hthreshold.trans hsize)

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open scoped BigOperators

/-- Keep precisely the bonds meeting the new site at most once. -/
def CavityGood {q N : ℕ} (x : Fin (q+1) → Fin (N+1)) : Prop :=
  ∀ i j, x i=0 → x j=0 → i=j

abbrev CavityIndex (q N : ℕ) :=
  (Fin (q+1) → Fin N) ⊕ (Fin (q+1) × (Fin q → Fin N))

def cavityIndexMap {q N : ℕ} : CavityIndex q N → (Fin (q+1) → Fin (N+1))
  | .inl x => fun i => (x i).succ
  | .inr z => z.1.insertNth 0 (fun i => (z.2 i).succ)

lemma cavityIndexMap_inr_zero_iff {q N : ℕ} (j : Fin (q+1)) (x : Fin q → Fin N)
    (i : Fin (q+1)) : cavityIndexMap (.inr (j,x)) i=0 ↔ i=j := by
  classical
  by_cases h : i=j
  · subst i
    simp [cavityIndexMap]
  · have hh : i ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact h
    obtain ⟨k,rfl⟩ := hh
    simp [cavityIndexMap,Fin.succAbove_ne]

lemma cavityIndexMap_good {q N : ℕ} (z : CavityIndex q N) : CavityGood (cavityIndexMap z) := by
  cases z with
  | inl x => intro i j hi; simp [cavityIndexMap] at hi
  | inr z =>
    intro i j hi hj
    exact (cavityIndexMap_inr_zero_iff _ _ _).mp hi |>.trans
      ((cavityIndexMap_inr_zero_iff _ _ _).mp hj).symm

lemma cavityIndexMap_injective {q N : ℕ} : Function.Injective (@cavityIndexMap q N) := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      congr 1
      funext i
      exact Fin.succ_injective N (congrFun h i)
    | inr z =>
      have hh := congrFun h z.1
      simp [cavityIndexMap] at hh
  | inr z =>
    cases b with
    | inl y =>
      have hh := congrFun h z.1
      simp only [cavityIndexMap,Fin.insertNth_apply_same] at hh
      exact (Fin.succ_ne_zero _ hh.symm).elim
    | inr w =>
      rcases z with ⟨j,x⟩
      rcases w with ⟨k,y⟩
      have hjk : j=k := by
        apply (cavityIndexMap_inr_zero_iff k y j).mp
        rw [← h]
        simp [cavityIndexMap]
      subst k
      congr 2
      funext i
      have hh := congrFun h (j.succAbove i)
      simpa [cavityIndexMap] using hh

lemma cavityIndexMap_surjective_good {q N : ℕ} (x : Fin (q+1) → Fin (N+1))
    (hx : CavityGood x) : ∃ z : CavityIndex q N, cavityIndexMap z=x := by
  classical
  by_cases h : ∃ i,x i=0
  · obtain ⟨j,hj⟩ := h
    have hn (i : Fin q) : x (j.succAbove i)≠0 := by
      intro hi
      exact Fin.succAbove_ne j i (hx _ _ hi hj)
    refine ⟨.inr (j,fun i => (x (j.succAbove i)).pred (hn i)),?_⟩
    funext i
    by_cases he : i=j
    · subst i
      simpa [cavityIndexMap] using hj.symm
    · have hh : i ∈ Set.range j.succAbove := by rw [Fin.range_succAbove]; exact he
      obtain ⟨k,rfl⟩ := hh
      simp [cavityIndexMap]
  · have hn (i : Fin (q+1)) : x i≠0 := fun hi => h ⟨i,hi⟩
    exact ⟨.inl (fun i => (x i).pred (hn i)),funext (fun i => Fin.succ_pred (x i) (hn i))⟩

noncomputable def cavityGoodEquiv (q N : ℕ) : CavityIndex q N ≃ {x // @CavityGood q N x} :=
  Equiv.ofBijective (fun z => ⟨cavityIndexMap z,cavityIndexMap_good z⟩) ⟨
    fun _ _ h => cavityIndexMap_injective (congrArg Subtype.val h),
    fun x => by
      obtain ⟨z,hz⟩ := cavityIndexMap_surjective_good x.val x.property
      exact ⟨z,Subtype.ext hz⟩⟩

noncomputable instance cavityGoodFintype (q N : ℕ) : Fintype {x // @CavityGood q N x} :=
  Fintype.ofFinite _

lemma sum_cavityGood {q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : (Fin (q+1) → Fin (N+1)) → A) :
    (∑ x : {x // @CavityGood q N x},f x.val) =
      (∑ x : Fin (q+1) → Fin N,f (fun i => (x i).succ))+
      ∑ j : Fin (q+1), ∑ x : Fin q → Fin N,f (j.insertNth 0 (fun i => (x i).succ)) := by
  classical
  rw [← Equiv.sum_comp (cavityGoodEquiv q N)]
  simp [cavityGoodEquiv,Equiv.ofBijective,cavityIndexMap,Fintype.sum_prod_type]

open Classical in
lemma sum_cavityKeep {q N : ℕ} {A : Type*} [AddCommMonoid A]
    (f : (Fin (q+1) → Fin (N+1)) → A) :
    (∑ x,if CavityGood x then f x else 0) =
      (∑ x : Fin (q+1) → Fin N,f (fun i => (x i).succ))+
      ∑ z : Fin (q+1) × (Fin q → Fin N),f (z.1.insertNth 0 (fun i => (z.2 i).succ)) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := CavityGood) _ (by simp)]
  rw [sum_cavityGood,Fintype.sum_prod_type]

end DilutedSpinGlass

end

end OAI
