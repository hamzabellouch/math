import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryWords

namespace OAI

section
section
namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

noncomputable def rawContact (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) : ℝ :=
  if a ∈ C.1 then if mark = none then 1 else 0 else
    match mark with
    | none => 0
    | some e => G.contactWeight order B C.1 a p w ω e

lemma rawContact_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (C : ClusterObject V E) (ω : E → Prop) (mark : Option E) :
    0 ≤ G.rawContact order B a p w C ω mark := by
  unfold rawContact
  split_ifs
  · norm_num
  · norm_num
  · cases mark with
    | none => exact le_rfl
    | some e => exact G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e

lemma rawContact_sum (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E) (ω : E → Prop) :
    (∑ mark, G.rawContact order B a p w C ω mark) =
      G.scheduledContact order B a p w C ω := by
  unfold rawContact scheduledContact
  split_ifs with ha
  · simp
  · rw [Fintype.sum_option]
    simp only [zero_add]
    exact G.sum_contactWeight order B C.1 a p w ω

lemma contactKernel_le_raw (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (C : ClusterObject V E) (ω : E → Prop) (mark : Option E)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hroot : c ≤ prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)) :
    G.contactKernel order B a p w C ω mark ≤ c⁻¹ * G.rawContact order B a p w C ω mark := by
  unfold contactKernel rawContact
  split_ifs with ha hm
  · rw [mul_one]
    exact (one_le_inv₀ hc).mpr hc1
  · simp
  · cases mark with
    | none => simp
    | some e =>
      rw [← div_eq_inv_mul]
      exact div_le_div_of_nonneg_left (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e) hc hroot

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma anchorSet_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchorSet d x n h = anchorSet d x n h' := by
  simp only [anchorSet,anchors_sides d x n h h' hs]

def scheduledAnchor (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : V :=
  x (nextIndex d k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k))

def scheduledTargets (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool) (k : ℕ) : Set V :=
  anchorSet d x k (historyPrefix n (fromWords n b (fun _ => (none : Option E))) k)

lemma scheduledAnchor_eq (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m : Fin n → Option E) (k : ℕ) (hk : k≤n) :
    scheduledAnchor (E := E) d x n b k = x (nextIndex d k (historyPrefix n (fromWords n b m) k)) := by
  rw [scheduledAnchor,nextIndex_sides d k _ _ (prefix_fromWords n b _ m k hk)]

lemma scheduledTargets_eq (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m : Fin n → Option E) (k : ℕ) (hk : k≤n) :
    scheduledTargets (E := E) d x n b k = anchorSet d x k (historyPrefix n (fromWords n b m) k) := by
  rw [scheduledTargets,anchorSet_sides d x k _ _ (prefix_fromWords n b _ m k hk)]

lemma prefix_succ_fst (n : ℕ) (h : History E n) (k : ℕ) (hk : k<n) :
    (historyPrefix n h (k+1)).1 = historyPrefix n h k := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k; rw [prefix_self,prefix_last]
    · have hk' : k<n := by omega
      rw [prefix_prev n h (k+1) (by omega),prefix_prev n h k hk'.le]
      exact ih h.1 hk'

lemma scheduledTargets_anchors (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (k : ℕ) (hk : k≤n) :
    scheduledTargets (E := E) d x n b k =
      BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) k := by
  induction k with
  | zero =>
    ext v
    simp [scheduledTargets,anchorSet,anchors,BondGraph.anchorSet,or_comm]
  | succ k ih =>
    have hi := ih (by omega)
    unfold scheduledTargets at *
    rw [anchorSet_step,prefix_succ_fst n _ k (by omega),hi]
    ext v
    simp only [BondGraph.anchorSet,Set.mem_insert_iff,Set.mem_union,Set.mem_image,Set.mem_ofPred_eq]
    constructor
    · rintro (rfl|hv)
      · exact Or.inr ⟨k,by omega,rfl⟩
      · rcases hv with hv|⟨j,hj,hv⟩
        · exact Or.inl hv
        · exact Or.inr ⟨j,by omega,hv⟩
    · rintro (hv|⟨j,hj,hv⟩)
      · exact Or.inr (Or.inl hv)
      · by_cases he : j=k
        · subst j; exact Or.inl hv.symm
        · exact Or.inr (Or.inr ⟨j,by omega,hv⟩)

section Products
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable def rawProduct : (n : ℕ) → History E n → (E → Prop) → ℝ
  | 0, _, _ => 1
  | n+1, h, ω => rawProduct n h.1 ω *
      G.rawContact order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
        (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2

lemma rawProduct_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (n : ℕ) (h : History E n) (ω : E → Prop) :
    0 ≤ rawProduct G order d x p w n h ω := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih h.1) (G.rawContact_nonneg order _ _ hp w h0 h1 _ ω _)

lemma density_le_rawProduct (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (r₀ : (E → Prop) → ℝ) (hr₀ : ∀ ω, 0 ≤ r₀ ω)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (n : ℕ) (h : History E n) (ω : E → Prop) :
    density G order d x p w r₀ n h ω ≤
      r₀ ω * (c⁻¹)^n * rawProduct G order d x p w n h ω := by
  induction n with
  | zero => simp only [density,rawProduct,pow_zero,mul_one,le_refl]
  | succ n ih =>
    rw [density,rawProduct,pow_succ]
    have hr := root_bound G hd x w (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le) hc1 hconn n h.1
    have hk := G.contactKernel_le_raw order (anchorSet d x n h.1)
      (x (nextIndex d n h.1)) hp w h0 h1 (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 hc hc1 hr
    have hpos := rawProduct_nonneg G order d x p w hp h0 h1 n h.1 ω
    have hraw := G.rawContact_nonneg order (anchorSet d x n h.1)
      (x (nextIndex d n h.1)) hp w h0 h1 (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2
    split_ifs
    · calc
        _ ≤ (r₀ ω * (c⁻¹)^n * rawProduct G order d x p w n h.1 ω) *
            (c⁻¹ * G.rawContact order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
              (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2) :=
          mul_le_mul (ih h.1) hk (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
            (mul_nonneg (mul_nonneg (hr₀ ω) (pow_nonneg (inv_nonneg.mpr hc.le) n)) hpos)
        _ = _ := by ring
    · exact mul_nonneg (mul_nonneg (hr₀ ω)
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hc.le) n) (inv_nonneg.mpr hc.le)))
        (mul_nonneg hpos hraw)

noncomputable def scheduleWeight (n : ℕ) (b : Fin n → Bool)
    (i : Fin n) (ω : E → Prop) (m : Option E) : ℝ :=
  G.rawContact order (scheduledTargets (E := E) d x n b i.val)
    (scheduledAnchor (E := E) d x n b i.val) p w
    (G.clusterObject ω (scheduledTargets (E := E) d x n b i.val)) ω m

lemma rawProduct_eq_finprod (n : ℕ) (h : History E n) (ω : E → Prop) :
    rawProduct G order d x p w n h ω =
      ∏ i : Fin n, G.rawContact order (anchorSet d x i.val (historyPrefix n h i.val))
        (x (nextIndex d i.val (historyPrefix n h i.val))) p w
        (G.clusterObject ω (anchorSet d x i.val (historyPrefix n h i.val))) ω (marks n h i) := by
  induction n with
  | zero => simp only [rawProduct,Fin.prod_univ_zero]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc,rawProduct,ih h.1]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_castSucc,prefix_prev n h i.val i.isLt.le,marks,Fin.snoc_castSucc]
    · simp only [Fin.val_last,prefix_last,marks,Fin.snoc_last]

lemma rawProduct_words (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) (ω : E → Prop) :
    rawProduct G order d x p w n (fromWords n b m) ω =
      ∏ i, scheduleWeight G order d x p w n b i ω (m i) := by
  rw [rawProduct_eq_finprod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [scheduleWeight,scheduledTargets_eq d x n b m i.val i.isLt.le,
    scheduledAnchor_eq d x n b m i.val i.isLt.le,marks_fromWords]

end Products
end CriticalPercolation.BinaryLaw
end
end

end OAI
