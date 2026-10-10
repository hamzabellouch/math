import OAI.Combinatorics.KMedian.Binary.InstanceParserProgram
import OAI.Combinatorics.KMedian.Binary.BinaryAutoExtras
import OAI.Combinatorics.KMedian.Programs.FinsetMaskProgram

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery.CheckedInput

open MetricKMedian MetricKMedian.Binary MetricKMedian.Binary.Automatic
open MetricKMedian.Binary.Automatic.Poly
open MetricKMedian.InstanceProgram (Raw view)
open MetricKMedian.SparseGraph.ListOperation (Row Table setView)

def n (x : Raw) : ℕ := x.1.2.length
def distance (x : Raw) (i j : ℕ) : ℚ := (x.2.2[i]?.getD [])[j]?.getD 0
def mask (x : Row) (m : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x[i.val]?.getD false)
def rows (x : Raw) : List ℕ := List.range (n x)

def metricTest (x : Raw) : Bool :=
  ((rows x).map (fun i => ((rows x).map (fun j =>
    decide (0 ≤ distance x i j) &&
    (decide (distance x i j = 0) == decide (i = j)) &&
    decide (distance x i j = distance x j i) &&
    (((rows x).map (fun k =>
      decide (distance x i k ≤ distance x i j + distance x j k))).all id))).all id)).all id

def valid (x : Raw) : Bool :=
  decide (0 < x.2.1) && decide (x.2.1 ≤ (x.1.2.filter id).length) && metricTest x

@[fun_prop] theorem distance_poly : Poly (fun x : Raw × (ℕ × ℕ) =>
    distance x.1 x.2.1 x.2.2) := by
  unfold distance
  fun_prop

@[fun_prop] theorem rows_poly : Poly rows := by
  exact list_indices.comp (show Poly (fun x : Raw => x.1.2) by fun_prop)

@[fun_prop] theorem bool_beq_poly : Poly (fun x : Bool × Bool => x.1 == x.2) := by
  have he : (fun x : Bool × Bool => x.1 == x.2) =
      (fun x => if x.1 then x.2 else !x.2) := by
    funext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  rw [he]
  fun_prop

@[fun_prop] theorem valid_poly : Poly valid := by
  unfold valid metricTest
  fun_prop

lemma mask_card (r : Row) : (mask r r.length).card = (r.filter id).length := by
  have he : List.ofFn (fun i : Fin r.length => r[i.val]?.getD false) = r := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  have hc := MetricKMedian.EncodingLists.length_filter_ofFn
    (fun i : Fin r.length => r[i.val]?.getD false) id
  rw [he] at hc
  exact hc.symm

lemma metricTest_spec {x : Raw} (h : metricTest x = true) (i j : Fin (n x)) :
    0 ≤ distance x i j ∧
    (distance x i j = 0 ↔ i = j) ∧
    distance x i j = distance x j i ∧
    ∀ k : Fin (n x), distance x i k ≤ distance x i j + distance x j k := by
  simp only [metricTest, List.all_map, List.all_eq_true, rows, List.mem_range,
    Function.comp_apply, id_eq, Bool.and_eq_true_iff, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩ := h i i.isLt j j.isLt
  refine ⟨h₀, ?_, h₂, fun k => h₃ k k.isLt⟩
  simpa only [decide_eq_decide, Fin.ext_iff] using h₁

def ofValid (x : Raw) (h : valid x = true) : Instance where
  n := n x
  distance i j := distance x i j
  clients := mask x.1.1 (n x)
  facilities := mask x.1.2 (n x)
  k := x.2.1
  distance_nonneg i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).1
  distance_eq_zero i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.1
  distance_symm i j := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.2.1
  distance_triangle i j k := (metricTest_spec (Bool.and_eq_true_iff.mp h).2 i j).2.2.2 k
  k_pos := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  k_le := by
    rw [n, mask_card]
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

def fallback : Instance where
  n := 1
  distance _ _ := 0
  clients := ∅
  facilities := Finset.univ
  k := 1
  distance_nonneg _ _ := le_rfl
  distance_eq_zero i j := ⟨fun _ => Subsingleton.elim i j, fun _ => rfl⟩
  distance_symm _ _ := rfl
  distance_triangle _ _ _ := by norm_num
  k_pos := le_rfl
  k_le := by simp

def checked (x : Raw) : Instance := if h : valid x = true then ofValid x h else fallback

def normalized (x : Raw) : Raw :=
  (((rows x).map (fun i => x.1.1[i]?.getD false), x.1.2),
    (x.2.1, (rows x).map (fun i => (rows x).map (fun j => distance x i j))))

@[fun_prop] theorem normalized_poly : Poly normalized := by
  unfold normalized
  fun_prop

lemma mask_view (r : Row) (m : ℕ) :
    setView (mask r m) = (List.range m).map (fun i => r[i]?.getD false) := by
  apply List.ext_getElem
  · simp [setView]
  · intro i h₁ h₂
    simp [setView, mask]

private lemma range_map {α : Type*} (m : ℕ) (f : ℕ → α) :
    (List.range m).map f = List.ofFn (fun i : Fin m => f i.val) := by
  apply List.ext_getElem <;> simp

lemma normalized_view (x : Raw) (h : valid x = true) : normalized x = view (ofValid x h) := by
  simp only [normalized, view, ofValid, mask_view, rows, n]
  have hr : (List.range x.1.2.length).map (fun i => x.1.2[i]?.getD false) = x.1.2 := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [h₂]
  rw [hr]
  simp only [range_map]

noncomputable def program : PolyProgram enc InstanceProgram.encode checked := by
  let p := (MetricKMedian.Binary.Automatic.Poly.ite valid_poly normalized_poly
    (MetricKMedian.Binary.Automatic.Poly.const (α := Raw) (view fallback))).program
  exact p.recode id (fun _ => rfl) (fun x => by
    change enc (if valid x = true then normalized x else view fallback) = enc (view (checked x))
    by_cases h : valid x = true
    · simp only [checked, ite_eq_left h, dite_eq_left h]
      exact congrArg enc (normalized_view x h)
    · simp only [checked, ite_eq_right h, dite_eq_right h])

lemma distance_view (I : Instance) (i j : Fin I.n) :
    distance (view I) i j = I.distance i j := by
  simp [distance, view, i.isLt, j.isLt]

lemma valid_view (I : Instance) : valid (view I) = true := by
  have hc : ((setView I.facilities).filter id).length = I.facilities.card :=
    MetricKMedian.EncodingLists.bool_card I.facilities
  change (decide (0 < I.k) && decide (I.k ≤ (setView I.facilities |>.filter id).length) &&
    metricTest (view I)) = true
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  refine ⟨⟨by exact decide_eq_true (by have := I.k_pos; omega),
    by simpa only [hc, decide_eq_true_iff] using I.k_le⟩, ?_⟩
  simp only [metricTest, rows, n, view, setView, List.length_ofFn, List.all_map,
    List.all_eq_true, List.mem_range, Function.comp_apply, id_eq,
    Bool.and_eq_true_iff, beq_iff_eq]
  intro i hi j hj
  have he (a b : ℕ) (ha : a < I.n) (hb : b < I.n) :
      distance (view I) a b = I.distance ⟨a, ha⟩ ⟨b, hb⟩ := distance_view I ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply decide_eq_true
    change 0 ≤ distance (view I) i j
    rw [he i j hi hj]
    exact I.distance_nonneg _ _
  · apply _root_.decide_eq_decide.mpr
    change distance (view I) i j = 0 ↔ i = j
    rw [he i j hi hj, I.distance_eq_zero]
    simp
  · apply decide_eq_true
    change distance (view I) i j = distance (view I) j i
    rw [he i j hi hj, he j i hj hi]
    exact I.distance_symm _ _
  · intro k hk
    apply decide_eq_true
    change distance (view I) i k ≤ distance (view I) i j + distance (view I) j k
    rw [he i k hi hk, he i j hi hj, he j k hj hk]
    exact I.distance_triangle _ _ _

private lemma view_injective : Function.Injective view := by
  rintro ⟨N, d, C, F, k, h₁, h₂, h₃, h₄, h₅, h₆⟩
    ⟨M, d', C', F', k', h₁', h₂', h₃', h₄', h₅', h₆'⟩ hv
  have hn : N = M := by
    have hh := congrArg (fun x : Raw => x.1.2.length) hv
    simpa only [view, setView, List.length_ofFn] using hh
  subst M
  have hC : C = C' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.1.1) hv)
    exact Finset.ext (fun i => decide_eq_decide.mp (congrFun hh i))
  have hF : F = F' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.1.2) hv)
    exact Finset.ext (fun i => decide_eq_decide.mp (congrFun hh i))
  have hd : d = d' := by
    have hh := List.ofFn_injective (congrArg (fun x : Raw => x.2.2) hv)
    funext i
    exact List.ofFn_injective (congrFun hh i)
  have hk : k = k' := congrArg (fun x : Raw => x.2.1) hv
  subst C'
  subst F'
  subst d'
  subst k'
  rfl

lemma checked_view (I : Instance) : checked (view I) = I := by
  apply view_injective
  rw [checked, dite_eq_left (valid_view I), ← normalized_view (view I) (valid_view I)]
  simp [normalized, rows, n, view, setView, range_map, distance]

noncomputable def parseProgram : PolyProgram id InstanceProgram.encode
    (fun xs => checked (InputParser.raw xs)) :=
  (BooleanLists.packProgram.comp InputParser.rawProgram).comp program

end MetricKMedianRecovery.RefinedRecovery.CheckedInput

end OAI
