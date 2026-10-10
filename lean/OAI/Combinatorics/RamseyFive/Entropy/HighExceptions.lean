import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Tail
import OAI.Combinatorics.RamseyFive.Decoding.Threshold

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.HighPlaneBudget

section
open Module GreedyTraining ProjectiveTraining HighParameters
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]
  {I : Type*} [LinearOrder I]
  (F : Finset I) (hF : F.Nonempty) (P : I → Submodule K V) (X : Finset (ℙ K V))

lemma plane_density_le : (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
    ProjectiveIncidence.Q (Nat.card K) 3 ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).trans' Nat.zero_lt_one
  have hQ : (0:ℝ)<ProjectiveIncidence.Q (Nat.card K) 3 := by
    exact_mod_cast ProjectiveIncidence.Q_pos (Nat.card K) 3
  apply (div_le_div_iff₀ hQ hq).mpr
  have hh := ProjectiveIncidence.Q_recurrence (q := Nat.card K) (d := 3) (by omega)
  have hh' : (ProjectiveIncidence.Q (Nat.card K) 3:ℝ)=
      (Nat.card K:ℝ)*ProjectiveIncidence.Q (Nat.card K) 2+1 := by exact_mod_cast hh
  rw [hh']
  nlinarith

noncomputable def highExceptions (L : Finset (Submodule K V)) (J : ℕ)
    (a χ : ℝ) (Y : Finset (ℙ K V)) : Finset (ℙ K V) :=
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  let M := threshold q n a
  let C := HighParameters.cap q a
  let D := degree q n a χ
  largeCellIntersections F hF P X (headIndex F hF (fun i => flatPoints (P i)) X J C) (n*a/1024) ∪
  (Y.filter fun x => D ≤ (headAt F hF P X L J C M (n*a/1024) x).card) ∪
  (Y.filter fun x => D ≤ ((tailPlanes F hF P X L J C M).filter fun A => x.submodule ≤ A).card)

theorem high_exceptions_card (hP : ∀ i ∈ F, finrank K (P i) = 4)
    (hcover : ∀ A : Submodule K V, finrank K A = 4 → ∃ i ∈ F, P i = A)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (J : ℕ) (a χ : ℝ) (Y : Finset (ℙ K V))
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hnq : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2) (hχ : 0≤χ) :
    ((highExceptions F hF P X L J a χ Y).card:ℝ) ≤
      3145728*(Nat.card K:ℝ)^2/a^2 +
      ((X.card:ℝ)^2*a^3/(Nat.card K:ℝ)^3)*Real.exp (-χ) +
      36864*(Nat.card K:ℝ)^2*Real.exp (-2*χ) := by
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  let M := threshold q n a
  let C := HighParameters.cap q a
  let D := degree q n a χ
  let u := multiplicity q n a
  let H := headIndex F hF (fun i => flatPoints (P i)) X J C
  let E₀ := largeCellIntersections F hF P X H (n*a/1024)
  let E₁ := Y.filter fun x => D ≤ (headAt F hF P X L J C M (n*a/1024) x).card
  let E₂ := Y.filter fun x => D ≤ ((tailPlanes F hF P X L J C M).filter fun A => x.submodule ≤ A).card
  have hq : 1≤q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : 0<n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨hM,hline,hlineNum,hcapMean,hhyperNum,hlarge⟩ := high_budget_conditions hq hn' ha ha2 hnq hhigh
  have hHC : (H:ℝ)*(C:ℝ)≤n := by
    dsimp [H,n]
    exact_mod_cast head_length_bound F hF (fun i => flatPoints (P i)) X J C
  have hHM : H*(Nat.card K+1)≤M := by
    have hh := head_length_condition hq hn' ha ha2 hhigh (Nat.cast_nonneg H) hHC
    dsimp [q,n] at hh
    exact_mod_cast hh
  have hdens := plane_density_le (K := K)
  have hheadMean := head_mean_condition hq hn' ha ha2 hhigh hdens
  have htailMean := tail_mean_condition hq hn' ha ha2 hnq hhigh hdens
  have hD := degree_multiplicity_condition hq hn' ha ha2 hnq hχ
  have hE₀ : (E₀.card:ℝ)≤3145728*q^2/a^2 := by
    apply large_exception_bound hq hn' ha
    have hh := largeCellIntersections_budget F hF P X hP H (n*a/1024) (by positivity)
    have he : (ProjectiveIncidence.Q (Nat.card K) 2:ℝ)=q^2+q+1 := by
      simp [ProjectiveIncidence.Q,Finset.sum_range_succ,q]
      ring
    simpa only [he] using hh
  have hE₁ : (E₁.card:ℝ)≤(n^2*a^3/q^3)*Real.exp (-χ) := by
    apply head_exception_bound hq hn' ha ha2 hhigh (Nat.cast_nonneg E₁.card) (Nat.cast_nonneg H) hHC
    exact head_exceptions F hF P X hP L hL J C M hM hHM (n*a/1024) hheadMean D Y
  have hE₂ : (E₂.card:ℝ)≤36864*q^2*Real.exp (-2*χ) := by
    rw [neg_mul]
    apply tail_exception_bound (χ := χ) hq hn' ha ha2 hnq hhigh (Nat.cast_nonneg E₂.card)
    apply tail_exceptions F hF P X hcover L hL J C M u D hM
    · dsimp [q,n] at hline
      exact_mod_cast hline
    · dsimp [q,n] at hlineNum
      exact_mod_cast hlineNum
    · exact htailMean
    · exact hhyperNum
    · dsimp [q,n] at hlarge
      exact_mod_cast hlarge
    · exact hD
  have hun : (E₀ ∪ E₁ ∪ E₂).card ≤ E₀.card+E₁.card+E₂.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hun' : ((E₀ ∪ E₁ ∪ E₂).card:ℝ) ≤ (E₀.card:ℝ)+E₁.card+E₂.card := by exact_mod_cast hun
  exact hun'.trans (by dsimp [q,n] at *; linarith)

theorem high_pairs (hdim : finrank K V = 5)
    (G : Finset (Submodule K V)) (hG : ∀ A ∈ G, finrank K A = 4)
    (L : Finset (Submodule K V)) (hL : ∀ A ∈ L, finrank K A = 3)
    (hcomplete : ∀ A : Submodule K V, finrank K A = 3 → A ∈ L)
    (J : ℕ) (a χ : ℝ) (Y : Finset (ℙ K V)) (x : ℙ K V) (hxY : x ∈ Y)
    (hxG : ∀ A ∈ G,x.submodule ≤ A)
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2)
    (hx : x ∉ highExceptions F hF P X L J a χ Y) :
    (capturedPairs F hF P X G J (threshold (Nat.card K) X.card a) x).card ≤
      2*degree (Nat.card K) X.card a χ*(Nat.card K+1)^2 := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : (0:ℝ)<X.card := by exact_mod_cast hn
  have hHC : ((headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)):ℝ)*
      HighParameters.cap (Nat.card K) a ≤ X.card := by
    exact_mod_cast head_length_bound F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)
  have hHM := head_length_condition hq hn' ha ha2 hhigh
    (Nat.cast_nonneg (headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a))) hHC
  have hHM' : headIndex F hF (fun i => flatPoints (P i)) X J (HighParameters.cap (Nat.card K) a)*
      (Nat.card K+1) ≤ threshold (Nat.card K) X.card a := by exact_mod_cast hHM
  simp only [highExceptions,Finset.mem_union,not_or] at hx
  have hh := captured_pairs_outside_exceptions F hF P X hdim G hG L hL hcomplete J
    (HighParameters.cap (Nat.card K) a) (threshold (Nat.card K) X.card a) hHM'
    (X.card*a/1024) (degree (Nat.card K) X.card a χ) (degree (Nat.card K) X.card a χ)
    Y x hxY hxG hx.1.1 hx.1.2 hx.2
  simpa only [two_mul] using hh

end

open Module RichPlaneGeometry HighParameters HyperplaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

noncomputable def residualPlanes (L : Finset (Submodule K V))
    (X : Finset (ℙ K V)) (M : ℕ) :=
  L.filter fun A => M ≤ (X.filter fun x => x.submodule ≤ A).card

lemma capped_plane_exceptions (L : Finset (Submodule K V))
    (hL : ∀ A ∈ L, finrank K A = 3) (X : Finset (ℙ K V))
    (M C u D : ℕ) (hMpos : 0<M)
    (hcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ C)
    (hline : 2*(Nat.card K+1)≤M) (hnum : 2*X.card≤u*M)
    (hmean : 2*((ProjectiveIncidence.Q (Nat.card K) 2:ℝ)/
      ProjectiveIncidence.Q (Nat.card K) 3)*C≤M)
    (hhnum : 4*(Nat.card K:ℝ)^2*C≤(u:ℝ)*M^2)
    (hlarge : 64*X.card≤M^2) (hD : 8*(2*u+1)≤D) (Y : Finset (ℙ K V)) :
    ((Y.filter fun x => D≤((residualPlanes L X M).filter fun A =>
      x.submodule≤A).card).card:ℝ)*D^2*M^2≤4096*(X.card:ℝ)^2*(2*(u:ℝ)+1)^2 := by
  let R := residualPlanes L X M
  have hrank : ∀ A∈R, finrank K A=3 := fun A hA => hL A (Finset.mem_filter.mp hA).1
  have hrich : ∀ A∈R, M≤(X.filter fun x => x.submodule≤A).card :=
    fun _ hA => (Finset.mem_filter.mp hA).2
  obtain ⟨hl,hh⟩ := multiplicity_budgets R hrank X M C u hMpos hrich hcap
    hline hnum hmean hhnum
  have hr := capped_rich_plane_count R hrank X M C u hMpos hrich hcap
    hline hnum hmean hhnum hlarge
  have he := RichPlaneOverlap.exceptional_centers R hrank u hl hh Y D hD
  have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(R.card:ℝ)*M) hr 2
  calc
    _ ≤ (16*(R.card:ℝ)^2)*(M:ℝ)^2 := mul_le_mul_of_nonneg_right he (sq_nonneg _)
    _ = 16*((R.card:ℝ)*M)^2 := by ring
    _ ≤ 16*(16*X.card*(2*(u:ℝ)+1))^2 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

noncomputable def residualExceptions (L : Finset (Submodule K V))
    (X Y : Finset (ℙ K V)) (a χ : ℝ) :=
  Y.filter fun x => degree (Nat.card K) X.card a χ ≤
    ((residualPlanes L X (threshold (Nat.card K) X.card a)).filter fun A => x.submodule≤A).card

theorem residual_exceptions_card (L : Finset (Submodule K V))
    (hL : ∀ A∈L,finrank K A=3) (X Y : Finset (ℙ K V)) (a χ : ℝ)
    (hn : 0<X.card) (ha : 0<a) (ha2 : a≤2)
    (hnq : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5)
    (hhigh : 2097152*(Nat.card K:ℝ)^2≤X.card*a^2) (hχ : 0≤χ)
    (hcap : ∀ H : Submodule K V,finrank K H=4 →
      (X.filter fun x => x.submodule≤H).card≤HighParameters.cap (Nat.card K) a) :
    ((residualExceptions L X Y a χ).card:ℝ)≤36864*(Nat.card K:ℝ)^2*Real.exp (-2*χ) := by
  let q : ℝ := Nat.card K
  let n : ℝ := X.card
  have hq : 1≤q := by dsimp [q]; exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hn' : 0<n := by dsimp [n]; exact_mod_cast hn
  obtain ⟨hM,hline,hlineNum,_,hhyperNum,hlarge⟩ := high_budget_conditions hq hn' ha ha2 hnq hhigh
  have hmean := tail_mean_condition hq hn' ha ha2 hnq hhigh (plane_density_le (K := K))
  have hD := degree_multiplicity_condition hq hn' ha ha2 hnq hχ
  rw [neg_mul]
  apply tail_exception_bound (χ := χ) hq hn' ha ha2 hnq hhigh (Nat.cast_nonneg _)
  apply capped_plane_exceptions L hL X (threshold q n a) (HighParameters.cap q a)
    (multiplicity q n a) (degree q n a χ) hM hcap
  · dsimp [q,n] at hline
    exact_mod_cast hline
  · dsimp [q,n] at hlineNum
    exact_mod_cast hlineNum
  · exact hmean
  · exact hhyperNum
  · dsimp [q,n] at hlarge
    exact_mod_cast hlarge
  · exact hD

noncomputable def residualPairs (G : Finset (Submodule K V))
    (X : Finset (ℙ K V)) (M : ℕ) :=
  (G ×ˢ G).filter fun p => p.1 ≠ p.2 ∧ M≤(X.filter fun y => y.submodule≤p.1⊓p.2).card

theorem residual_pairs (hdim : finrank K V=5)
    (G : Finset (Submodule K V)) (hG : ∀ A∈G,finrank K A=4)
    (L : Finset (Submodule K V)) (hL : ∀ A∈L,finrank K A=3)
    (hcomplete : ∀ A : Submodule K V,finrank K A=3 → A∈L)
    (X Y : Finset (ℙ K V)) (a χ : ℝ) (x : ℙ K V) (hxY : x∈Y)
    (hxG : ∀ A∈G,x.submodule≤A) (hx : x∉residualExceptions L X Y a χ) :
    (residualPairs G X (threshold (Nat.card K) X.card a)).card≤
      degree (Nat.card K) X.card a χ*(Nat.card K+1)^2 := by
  let M := threshold (Nat.card K) X.card a
  let R := (residualPlanes L X M).filter fun A => x.submodule≤A
  have hh := pair_count_by_intersection (d := 4) hdim G hG R 3
    (fun A hA => hL A (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1)
    (residualPairs G X M) (Finset.filter_subset _ _) (by
      intro p hp
      obtain ⟨hp,hne,hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hcomplete _ (hyperplane_intersection_rank (d := 4) hdim
        p.1 p.2 (hG _ h1) (hG _ h2) hne),hpc⟩,le_inf (hxG _ h1) (hxG _ h2)⟩)
  have hc : R.card < degree (Nat.card K) X.card a χ := by
    apply Nat.lt_of_not_ge
    intro he
    exact hx (Finset.mem_filter.mpr ⟨hxY,he⟩)
  have he : (∑ i∈Finset.range (4+1-3),Nat.card K^i)=Nat.card K+1 := by
    norm_num [Finset.sum_range_succ,Nat.add_comm]
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_right _ hc.le)
end SharpRamseyFive.HighPlaneBudget

end OAI
