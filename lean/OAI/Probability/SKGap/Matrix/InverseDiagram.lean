import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing

inductive InverseDiagram where
  | empty
  | counterterm (rest : InverseDiagram)
  | arch (inside rest : InverseDiagram)
  deriving DecidableEq

namespace InverseDiagram

def degree : InverseDiagram → ℕ
  | .empty => 0
  | .counterterm d => d.degree + 1
  | .arch d e => d.degree + e.degree + 1

def blocks : InverseDiagram → List Bool
  | .empty => []
  | .counterterm d => false :: d.blocks
  | .arch d e => true :: (d.blocks ++ true :: e.blocks)

theorem blocks_degree (d : InverseDiagram) :
    ((d.blocks.map (fun b => if b then 1 else 2)).sum : ℕ) = 2 * d.degree := by
  induction d with
  | empty => rfl
  | counterterm d ih => simp only [blocks, List.map_cons, List.sum_cons, Bool.false_eq_true,
      ↓reduceIte, ih, degree]; omega
  | arch d e ihd ihe => simp only [blocks, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, ↓reduceIte, ihd, ihe, degree]; omega

def enumerate : ℕ → List InverseDiagram
  | 0 => [.empty]
  | n + 1 => (enumerate n).map .counterterm ++
      (List.finRange (n+1)).flatMap fun k =>
        (enumerate k.val).flatMap fun u =>
          (enumerate (n-k.val)).map (fun v => .arch u v)
termination_by n => n
decreasing_by all_goals omega

lemma mem_enumerate (d : InverseDiagram) (n : ℕ) : d ∈ enumerate n ↔ d.degree = n := by
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    cases n with
    | zero =>
      cases d <;> simp [enumerate, degree]
    | succ n =>
      rw [enumerate]
      cases d with
      | empty => simp [degree]
      | counterterm d =>
        simpa [degree] using ih n (by omega) d
      | arch u v =>
        simp only [List.mem_append, List.mem_map, List.mem_flatMap]
        constructor
        · rintro (⟨d, -, he⟩ | ⟨k, -, u', hu', v', hv', he⟩)
          · cases he
          · cases he
            have hu := (ih k.val (by omega) u).mp hu'
            have hv := (ih (n-k.val) (by omega) v).mp hv'
            simp only [degree]
            omega
        · intro hd
          have hu : u.degree < n+1 := by simp only [degree] at hd; omega
          refine Or.inr ⟨⟨u.degree, hu⟩, List.mem_finRange _, u, (ih _ hu u).mpr rfl,
            v, (ih _ (by omega) v).mpr ?_, rfl⟩
          change v.degree = n - u.degree
          simp only [degree] at hd
          omega

lemma nodup_arch_list (U V : List InverseDiagram) (hU : U.Nodup) (hV : V.Nodup) :
    (U.flatMap fun u => V.map (fun v => InverseDiagram.arch u v)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro u _
    exact (List.nodup_map_iff (fun v w h => (InverseDiagram.arch.inj h).2)).mpr hV
  · apply List.Pairwise.imp (fun {u v} huv => ?_) hU
    apply List.disjoint_left.mpr
    intro t htU htV
    obtain ⟨u', -, hu'⟩ := List.mem_map.mp htU
    obtain ⟨v', -, hv'⟩ := List.mem_map.mp htV
    exact huv (InverseDiagram.arch.inj (hu'.trans hv'.symm)).1

theorem enumerate_nodup (n : ℕ) : (enumerate n).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [enumerate]
    | succ n =>
      rw [enumerate, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact (List.nodup_map_iff (fun u v h => InverseDiagram.counterterm.inj h)).mpr
          (ih n (by omega))
      · apply List.nodup_flatMap.mpr
        constructor
        · intro k _
          exact nodup_arch_list _ _ (ih k.val k.isLt) (ih (n-k.val) (by omega))
        · apply List.Pairwise.imp (fun {k l} hkl => ?_) (List.nodup_finRange (n+1))
          apply List.disjoint_left.mpr
          intro t htK htL
          simp only [List.mem_flatMap, List.mem_map] at htK htL
          obtain ⟨u, hu, v, -, he⟩ := htK
          obtain ⟨u', hu', v', -, he'⟩ := htL
          have huu : u = u' := (InverseDiagram.arch.inj (he.trans he'.symm)).1
          have hk := (mem_enumerate u k.val).mp hu
          have hl := (mem_enumerate u' l.val).mp hu'
          apply hkl
          apply Fin.ext
          exact hk.symm.trans ((congrArg degree huu).trans hl)
      · intro t ht1 s ht2 he
        subst s
        obtain ⟨u, -, hu⟩ := List.mem_map.mp ht1
        simp only [List.mem_flatMap, List.mem_map] at ht2
        obtain ⟨k, -, a, -, b, -, ht⟩ := ht2
        cases hu.trans ht.symm

variable {ι : Type*} [Fintype ι]

def average (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

def value (j : ℝ) (a : ι → ℝ) : InverseDiagram → ι → ℝ
  | .empty, _ => 1
  | .counterterm d, i => -(j * average a) * a i * value j a d i
  | .arch u v, i => j * a i * average (fun k => a k * value j a u k) * value j a v i

def coefficient (j : ℝ) (a : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  ((enumerate n).map (fun d => value j a d i)).sum

@[simp] lemma coefficient_zero (j : ℝ) (a : ι → ℝ) (i : ι) :
    coefficient j a 0 i = 1 := by simp [coefficient, enumerate, value]

lemma average_add (x y : ι → ℝ) : average (x+y) = average x + average y := by
  simp [average, Finset.sum_add_distrib, add_div]

@[simp] lemma average_zero : average (0 : ι → ℝ) = 0 := by simp [average]

lemma average_list_sum {α : Type*} (l : List α) (f : α → ι → ℝ) :
    average (fun i => (l.map (fun u => f u i)).sum) =
      (l.map (fun u => average (f u))).sum := by
  induction l with
  | nil => simp [average]
  | cons u l ih =>
    simp only [List.map_cons, List.sum_cons]
    change average (f u + fun i => (l.map (fun v => f v i)).sum) = _
    rw [average_add, ih]

lemma sum_flatMap {α : Type*} {R : Type*} [AddMonoid R]
    (l : List α) (f : α → List R) : (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

lemma sum_arch (j : ℝ) (a : ι → ℝ) (U V : List InverseDiagram) (i : ι) :
    ((U.flatMap fun u => V.map (fun v => .arch u v)).map (fun d => value j a d i)).sum =
      j * a i * average (fun k => a k * (U.map (fun u => value j a u k)).sum) *
        (V.map (fun v => value j a v i)).sum := by
  simp only [List.map_flatMap, List.map_map, Function.comp_def, sum_flatMap, value,
    List.sum_map_mul_left]
  rw [List.sum_map_mul_right, List.sum_map_mul_left]
  congr 2
  rw [← average_list_sum]
  congr 1
  funext k
  exact List.sum_map_mul_left U (fun u => value j a u k) (a k)

lemma coefficient_succ (j : ℝ) (a : ι → ℝ) (n : ℕ) (i : ι) :
    coefficient j a (n+1) i = -(j * average a) * a i * coefficient j a n i +
      ∑ k : Fin (n+1), j * a i * average (fun u => a u * coefficient j a k.val u) *
        coefficient j a (n-k.val) i := by
  rw [coefficient, enumerate]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    value, List.sum_map_mul_left, List.map_flatMap, sum_flatMap]
  rw [Fin.sum_univ_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  simpa only [List.map_flatMap, List.map_map, Function.comp_def, sum_flatMap,
    value, List.sum_map_mul_left, coefficient] using
      sum_arch j a (enumerate k.val) (enumerate (n-k.val)) i

theorem coefficient_positive (j : ℝ) (a : ι → ℝ) (n : ℕ) (hn : 0 < n) (i : ι) :
    coefficient j a n i = 0 := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [coefficient_succ]
    have hs : (∑ k : Fin (n+1), j * a i * average (fun u => a u * coefficient j a k.val u) *
        coefficient j a (n-k.val) i) = j * a i * average a * coefficient j a n i := by
      rw [Finset.sum_eq_single (0 : Fin (n+1))]
      · simp
      · intro k _ hk
        have hk0 : 0 < k.val := by have hne : k.val ≠ 0 := fun he => hk (Fin.ext he); omega
        have hz (u : ι) : coefficient j a k.val u = 0 := ih k.val k.isLt hk0 u
        simp [hz, average]
      · simp
    rw [hs]
    ring

def predictionSeries (j : ℝ) (a : ι → ℝ) : PowerSeries (ι → ℝ) :=
  PowerSeries.mk fun n => fun i => if Even n then coefficient j a (n/2) i else 0

theorem predictionSeries_eq_one (j : ℝ) (a : ι → ℝ) : predictionSeries j a = 1 := by
  ext n i
  simp only [predictionSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst n
    simp
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    by_cases he : Even n
    · have hn2 : 0 < n/2 := by rcases he with ⟨k, hk⟩; omega
      simp [he, coefficient_positive j a (n/2) hn2 i, hn]
    · simp [he, hn]

end InverseDiagram
end SKGap.Noncrossing

noncomputable section

end
end
end
end

end OAI
