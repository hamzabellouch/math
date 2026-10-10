import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CommonL

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def cap (n : ℕ) (eps : ℝ) : ℕ := ⌈20*(n:ℝ)^2/eps⌉₊+1
lemma cap_pos (n : ℕ) (eps : ℝ) : 0 < cap n eps := by unfold cap; omega

lemma five_bound_lt_cap (n : ℕ) (hn : 0 < n) (eps : ℝ)
    (heps : 0 < eps) (hle : eps < 1) :
    5*((n:ℝ)^2/eps+n) < cap n eps := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hd : (n:ℝ)^2 ≤ (n:ℝ)^2/eps := by
    exact (le_div_iff₀ heps).mpr (mul_le_of_le_one_right (by positivity) hle.le)
  have hc : 20*(n:ℝ)^2/eps ≤ (⌈20*(n:ℝ)^2/eps⌉₊:ℝ) := Nat.le_ceil _
  simp only [cap,Nat.cast_add,Nat.cast_one]
  have hq : 0 < (n:ℝ)^2/eps := by positivity
  have hc' : 20*((n:ℝ)^2/eps) ≤ (⌈20*(n:ℝ)^2/eps⌉₊:ℝ) := by
    calc
      _ = 20*(n:ℝ)^2/eps := by ring
      _ ≤ _ := hc
  linarith

theorem factor_transfer (D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hn : 0 < D.card) (eps M A : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hM : 0 < M) (hMP : M ≤ LocalSearch.cost D O)
    (hPM : LocalSearch.cost D O ≤ D.card*M) (hA : 0 ≤ A) (hA5 : A ≤ 5)
    (hSbound : (cost (eps*M/D.card) (cap D.card eps) D S:ℝ) ≤
      A*(cost (eps*M/D.card) (cap D.card eps) D O:ℝ)) :
    LocalSearch.cost D S ≤ A*(1+eps)*LocalSearch.cost D O := by
  let u := eps*M/(D.card:ℝ)
  let C := cap D.card eps
  have hnR : (0:ℝ) < D.card := by exact_mod_cast hn
  have hu : 0 < u := div_pos (mul_pos heps hM) hnR
  have hupper := rounded_cost_upper u hu C D O hO
  have hquot : LocalSearch.cost D O/u ≤ (D.card:ℝ)^2/eps := by
    apply (div_le_iff₀ hu).mpr
    calc
      _ ≤ (D.card:ℝ)*M := hPM
      _ = ((D.card:ℝ)^2/eps)*u := by dsimp [u]; field_simp
  have hcapR : (cost u C D S:ℝ) < C := by
    calc
      _ ≤ A*(cost u C D O:ℝ) := hSbound
      _ ≤ 5*(cost u C D O:ℝ) := mul_le_mul_of_nonneg_right hA5 (Nat.cast_nonneg _)
      _ ≤ 5*((D.card:ℝ)^2/eps+D.card) := mul_le_mul_of_nonneg_left (hupper.trans (by linarith)) (by norm_num)
      _ < C := five_bound_lt_cap D.card hn eps heps heps1
  have hcap : cost u C D S < C := by exact_mod_cast hcapR
  calc
    _ ≤ u*(cost u C D S:ℝ) := original_cost_le u hu C D S hS hcap
    _ ≤ u*(A*(cost u C D O:ℝ)) := mul_le_mul_of_nonneg_left hSbound hu.le
    _ = A*(u*(cost u C D O:ℝ)) := by ring
    _ ≤ A*(u*(LocalSearch.cost D O/u+D.card)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hu.le) hA
    _ = A*(LocalSearch.cost D O+eps*M) := by dsimp [u]; field_simp
    _ ≤ A*(LocalSearch.cost D O+eps*LocalSearch.cost D O) :=
      mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left hMP heps.le]) hA
    _ = _ := by ring

end MetricKMedianRecovery.Rounding

namespace MetricKMedianRecovery.IndexedCopies
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

def tag (b : Bool) : V ↪ V × Bool := ⟨fun x => (x,b),by intro x y h; exact congrArg Prod.fst h⟩
def marked (b : Bool) (S : Finset V) : Finset (V × Bool) := S.map (tag b)

omit [PseudoMetricSpace V] in
lemma marked_card (b : Bool) (S : Finset V) : (marked b S).card = S.card := Finset.card_map _
omit [PseudoMetricSpace V] in
lemma marked_nonempty (b : Bool) (S : Finset V) : (marked b S).Nonempty ↔ S.Nonempty := Finset.map_nonempty
omit [PseudoMetricSpace V] in
lemma marked_subset (b : Bool) {S T : Finset V} (h : S ⊆ T) : marked b S ⊆ marked b T :=
  Finset.map_subset_map.mpr h

@[instance_reducible]
def metric : PseudoMetricSpace (V × Bool) := PseudoMetricSpace.induced Prod.fst inferInstance

lemma cost_marked (a b : Bool) (D S : Finset V) :
    @cost (V × Bool) metric (marked a D) (marked b S) = cost D S := by
  classical
  simp only [cost,marked,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hS : S.Nonempty
  · have hSm : (S.map (tag b)).Nonempty := Finset.map_nonempty.mpr hS
    simp only [connection,dite_eq_left hS,dite_eq_left hSm,Finset.inf'_map]
    rfl
  · have hSm : ¬(S.map (tag b)).Nonempty := by simpa only [Finset.map_nonempty]
    simp only [connection,dite_eq_right hS,dite_eq_right hSm]

omit [PseudoMetricSpace V] in

lemma project_set [DecidableEq V] (F : Finset V) (S : Finset (V × Bool))
    (hS : S ⊆ marked true F) :
    ∃ T ⊆ F, marked true T = S ∧ T.card = S.card := by
  let T := S.image Prod.fst
  have hT : T ⊆ F := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,he⟩ := Finset.mem_map.mp (hS hp)
    rw [←he]
    exact hq
  have he : marked true T = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hx
      obtain ⟨q,hq,hqy⟩ := Finset.mem_map.mp (hS hy)
      have heq : tag true x = y := by
        rw [←hqy] at hxy ⊢
        change q = x at hxy
        exact congrArg (tag true) hxy.symm
      exact heq.symm ▸ hy
    · intro hp
      obtain ⟨x,hx,heq⟩ := Finset.mem_map.mp (hS hp)
      apply Finset.mem_map.mpr
      refine ⟨x,Finset.mem_image.mpr ⟨p,hp,?_⟩,heq⟩
      rw [←heq]
      rfl
  exact ⟨T,hT,he,(marked_card true T).symm.trans (congrArg Finset.card he)⟩

end MetricKMedianRecovery.IndexedCopies

end OAI
