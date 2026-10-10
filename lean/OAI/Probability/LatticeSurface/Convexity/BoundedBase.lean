import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

abbrev Free {V : Type*} (pins : Set V) := {x : V // x ∉ pins}

noncomputable instance (priority := 2000) freeFintype {V : Type*} [Fintype V]
    (pins : Set V) : Fintype (Free pins) := Fintype.ofFinite _

def restore {V : Type*} (pins : Set V) (b : V → ℝ)
    (h : Free pins → ℝ) (x : V) : ℝ := if hx : x ∈ pins then b x else h ⟨x,hx⟩

def conditionalBody {V : Type*} (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    Set (Free pins → ℝ) :=
  {h | ∀ x y, G.Adj x y → |restore pins b h x - restore pins b h y| ≤ 1}

lemma continuous_restore {V : Type*} [Fintype V] (pins : Set V) (b : V → ℝ) (x : V) :
    Continuous (fun h : Free pins → ℝ => restore pins b h x) := by
  classical
  by_cases hx : x ∈ pins
  · simpa [restore, hx] using (continuous_const : Continuous (fun _ : Free pins → ℝ => b x))
  · simpa [restore, hx] using (continuous_apply (⟨x,hx⟩ : Free pins) : Continuous (fun h : Free pins → ℝ => h ⟨x,hx⟩))

lemma closed_conditionalBody {V : Type*} [Fintype V]
    (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) :
    IsClosed (conditionalBody G pins b) := by
  simp only [conditionalBody, ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _ =>
    isClosed_le ((continuous_restore pins b x).sub (continuous_restore pins b y)).abs continuous_const

lemma preserving_piOptionReal {N : Type*} [Fintype N] :
    MeasurePreserving (MeasurableEquiv.piOptionEquivProd (fun _ : Option N => ℝ)) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option N => ℝ)
  have hh : MeasurePreserving e.symm :=
    ⟨e.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option N => (volume : Measure ℝ))⟩
  exact hh.symm e.symm

def coordinateIndex (pins : Set V) (x : V) (hx : x ∉ pins) :
    Free pins ≃ Option (Free (insert x pins)) where
  toFun y := if hy : (y : V) = x then none else some ⟨y, by simpa [hy] using y.2⟩
  invFun o := match o with
    | none => ⟨x, hx⟩
    | some y => ⟨y, fun hp => y.2 (Or.inr hp)⟩
  left_inv := by
    intro y
    by_cases hy : (y : V) = x
    · simp only [dite_eq_left hy]
      exact Subtype.ext hy.symm
    · simp only [dite_eq_right hy]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some y =>
      have hn : (y : V) ≠ x := fun hh => y.2 (Or.inl hh)
      simp [hn]

def splitCoordinate (pins : Set V) (x : V) (hx : x ∉ pins) :
    (Free pins → ℝ) ≃ᵐ ((Free (insert x pins) → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Option (Free (insert x pins)) => ℝ)
    (coordinateIndex pins x hx)).trans (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ))

lemma preserving_splitCoordinate [Fintype V] (pins : Set V) (x : V) (hx : x ∉ pins) :
    MeasurePreserving (splitCoordinate pins x hx) :=
  preserving_piOptionReal.comp (volume_measurePreserving_piCongrLeft _ (coordinateIndex pins x hx))

lemma coordinate_restore (pins : Set V) (x : V) (hx : x ∉ pins) (b : V → ℝ)
    (h : Free (insert x pins) → ℝ) (t : ℝ) (y : V) :
    restore pins b ((splitCoordinate pins x hx).symm (h,t)) y =
      if y = x then t else restore (insert x pins) b h y := by
  by_cases hy : y = x
  · subst y
    simp [restore, splitCoordinate, MeasurableEquiv.piCongrLeft, coordinateIndex,
      MeasurableEquiv.piOptionEquivProd, hx]
    rfl
  · by_cases hyp : y ∈ pins
    · have hn : y ∈ insert x pins := Or.inr hyp
      simp [restore, hn, hy, hyp]
    · have hn : y ∉ insert x pins := by simpa [hy] using hyp
      simp [restore, hn, hy, hyp, splitCoordinate, MeasurableEquiv.piCongrLeft,
        coordinateIndex, MeasurableEquiv.piOptionEquivProd]
      rfl

lemma bound_along_walk (G : SimpleGraph V) (h : V → ℝ)
    (hh : ∀ x y, G.Adj x y → |h x-h y| ≤ 1) {x y : V} (p : G.Walk x y) :
    |h x-h y| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    calc
      |h u-h w| ≤ |h u-h v|+|h v-h w| := by
        simpa only [sub_add_sub_cancel] using abs_add_le (h u-h v) (h v-h w)
      _ ≤ 1+p.length := add_le_add (hh u v huv) ih
      _ = _ := by simp; ring

lemma volume_zeroBody_pos [Fintype V] (G : SimpleGraph V) (pins : Set V) :
    0 < volume (conditionalBody G pins (fun _ => 0)) := by
  let B : Set (Free pins → ℝ) := Icc (fun _ => -(1/2 : ℝ)) (fun _ => 1/2)
  have hb : B ⊆ conditionalBody G pins (fun _ => 0) := by
    intro h hh x y hxy
    have hh' : ∀ z, |restore pins (fun _ => 0) h z| ≤ 1/2 := by
      intro z
      by_cases hz : z ∈ pins
      · simp [restore, hz]
      · simpa [restore, hz] using abs_le.mpr ⟨hh.1 ⟨z,hz⟩,hh.2 ⟨z,hz⟩⟩
    calc
      |restore pins (fun _ => 0) h x-restore pins (fun _ => 0) h y| ≤
        |restore pins (fun _ => 0) h x|+|restore pins (fun _ => 0) h y| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (restore pins (fun _ => 0) h x) (-restore pins (fun _ => 0) h y)
      _ ≤ 1 := by linarith [hh' x, hh' y]
  have hpos : 0 < volume B := by
    rw [show B = Set.pi Set.univ (fun _ : Free pins => Icc (-(1/2 : ℝ)) (1/2)) by ext h; simp [B, Set.mem_Icc, Pi.le_def], MeasureTheory.volume_pi_pi]
    norm_num [Real.volume_Icc]
  exact hpos.trans_le (measure_mono hb)

end ExtremalEdges

end

end OAI
