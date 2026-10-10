import OAI.Combinatorics.PlanarL1.SecondaryFamily
import OAI.Combinatorics.PlanarL1.Dilation

namespace OAI


section

namespace PlanarL1.Columns.Model
open MeasureTheory
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable (A : Ambient M) {c t : ℝ} (hc : 0<c) (hcr : c≤4)

namespace BState
/-- The auxiliary fields are the actual finite recorded histories, with a lower
bound on every previously used scale. Empty fresh histories obey any bound. -/
structure Histories (S : BState M κ lam Ω μ) (t : ℝ) where
  history : Fin (S.count+1) → A.History c
  older : ∀ a j, t≤(history a).radius j
  recorded : ∀ a, (S.chart a).Recorded (history a) hc hcr

namespace Histories
variable {A hc hcr} {S : BState M κ lam Ω μ}

def weaken (H : Histories A hc hcr S t) {s : ℝ} (h : s≤t) : Histories A hc hcr S s where
  history := H.history
  older a j := h.trans (H.older a j)
  recorded := H.recorded

noncomputable def lift (H : Histories A hc hcr S t) : Histories A hc hcr S.lift t where
  history := H.history
  older := H.older
  recorded := H.recorded

noncomputable def ofOrdinary (S : OrdinaryState M κ Ω μ) :
    Histories A hc hcr (BState.ofOrdinary (lam := lam) S) t where
  history _ := Ambient.History.empty A c
  older _ j := Fin.elim0 j
  recorded _ := trivial

noncomputable def append (H : Histories A hc hcr S t)
    (B : SetSystem M Ω μ) (m : ℕ) (D : Fin m → BData M)
    (Z : Fin m → Threshold.Variables Ω μ) (choose : Fin (k+1) → ℝ → Option (Fin m))
    (hin : ∀ i H a, choose i H=some a → H∈(D a).band)
    (hcomp : ∀ i H a, choose i H=some a → (D a).Uses i)
    (hswitch : ∀ i j H, H∈M.heights i j → choose i H=choose j H)
    (hold : ∀ ω i H, choose i H=none →
      ((B.activity ω).active i H ↔ (S.sets.activity ω).active i H))
    (hnew : ∀ ω i H a (h : choose i H=some a),
      ((B.activity ω).active i H ↔ Threshold.active (Z a) H
        (κ*(D a).value lam i ⟨H,hin i H a h⟩) ω))
    (hD : ∀ a, (D a).Recorded (Ambient.History.empty A c) hc hcr) :
    Histories A hc hcr (S.append B m D Z choose hin hcomp hswitch hold hnew) t where
  history := Fin.addCases (m := m) (n := S.count+1) (motive := fun _ : Fin (m+(S.count+1)) => A.History c) (fun _ => Ambient.History.empty A c) H.history
  older a := by
    let P (Z : A.History c) : Prop := ∀ j, t≤Z.radius j
    change P (Fin.addCases (m := m) (n := S.count+1) (motive := fun _ : Fin (m+(S.count+1)) => A.History c) (fun _ => Ambient.History.empty A c) H.history a)
    refine Fin.addCases (m := m) (n := S.count+1) ?_ ?_ a
    · intro i
      rw [Fin.addCases_left]
      exact fun j => Fin.elim0 j
    · intro i
      rw [Fin.addCases_right]
      exact H.older i
  recorded a := by
    refine Fin.addCases (m := m) (n := S.count+1) ?_ ?_ a
    · intro i
      simpa only [BState.append, Fin.addCases_left] using hD i
    · intro i
      simpa only [BState.append, Fin.addCases_right] using H.recorded i

noncomputable def increment (H : Histories A hc hcr S t) {r s : ℝ}
    (sign : Fin (S.count+1) → Bool) (hr : 0<r) (hs : s≤r) (ht : s≤t)
    (hcross : ∀ a j, 10*r≤c*(H.history a).radius j)
    (hk : 0≤κ) (hsmall : κ*5≤1/2) (hlam : lam≤(1:ℝ≥0)/100)
    (hboundary : κ*(lam:ℝ)*10≤1/8) :
    Histories A hc hcr
      (S.increment A H.history sign hc hcr hr hcross H.recorded hk hsmall hlam hboundary) s where
  history a := (S.chart a).incrementHistory (H.history a) r (S.region A a) (sign a) hr (hcross a)
  older a := by
    cases he : S.chart a with
    | ordinary D =>
      intro j
      simpa only [BData.incrementHistory] using ht.trans (H.older a j)
    | ordered D =>
      intro j
      cases j using Fin.lastCases with
      | last => simpa only [BData.incrementHistory,Ambient.History.append,Fin.snoc_last] using hs
      | cast j => simpa only [BData.incrementHistory,Ambient.History.append,Fin.snoc_castSucc] using ht.trans (H.older a j)
  recorded a := S.increment_recorded A H.history sign hc hcr hr hcross H.recorded hk hsmall hlam hboundary a
end Histories
end BState

namespace BState.SecondaryStep
variable {J : Set ℝ} {root : Fin (k+1)} {S : BState M κ lam Ω μ}
variable (U : SecondaryStep S J root)
lemma newData_recorded (a : Fin (3*(k+1)*U.tree.depthCap+2)) :
    (U.newData a).Recorded (Ambient.History.empty A c) hc hcr := by
  classical
  unfold newData
  split_ifs
  · trivial
  · intro i T
    rw [Ambient.History.field_empty]
    rfl
  · trivial
end BState.SecondaryStep

namespace BState.SecondaryLayer
variable {S : BState M κ lam Ω μ} (B : SecondaryLayer S)
noncomputable def histories [SFinite μ] (H : Histories A hc hcr S t) :
    Histories A hc hcr B.apply t := by
  unfold apply
  apply H.lift.append
  intro a
  exact ((B.batch _).step _).newData_recorded A hc hcr _
end BState.SecondaryLayer
end PlanarL1.Columns.Model

end



section

open Set
namespace PlanarL1
/-- The distance to a literal image scales under a surjective homothety,
including the empty set convention for `infDist`. -/
lemma infDist_homothety {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) {q : ℝ} (hq : 0<q) (hd : ∀ x y, dist (f x) (f y)=q*dist x y)
    (x : X) (S : Set X) : Metric.infDist (f x) (f '' S)=q*Metric.infDist x S := by
  by_cases hs : S.Nonempty
  · apply le_antisymm
    · rw [mul_comm q]
      apply (div_le_iff₀ hq).mp
      apply (Metric.le_infDist hs).mpr
      intro y hy
      exact (div_le_iff₀ hq).mpr (by
        rw [mul_comm]
        exact (Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem f hy)).trans_eq (hd x y))
    · apply (Metric.le_infDist (hs.image f)).mpr
      rintro _ ⟨y,hy,rfl⟩
      rw [hd]
      exact mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hy) hq.le
  · have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simp only [he,Set.image_empty,Metric.infDist_empty,mul_zero]

namespace Increment
variable {q : ℝ} (hq : 0<q)
include hq
lemma clamp_scale (a b t : ℝ) : clamp (q*a) (q*b) (q*t)=q*clamp a b t := by
  unfold clamp
  rw [← mul_max_of_nonneg _ _ hq.le,← mul_min_of_nonneg _ _ hq.le]

lemma quadratic_scale (a b c d t : ℝ) :
    quadratic (q*a) (q*b) (q*c) (q*d) (q*t)=q*quadratic a b c d t := by
  unfold quadratic
  rw [clamp_scale hq]
  rw [← mul_sub]
  field_simp

lemma low_scale (a t : ℝ) : low (q*a) (q*t)=q*low a t := by
  unfold low
  rw [show 2*(q*a)=q*(2*a) by ring,quadratic_scale hq]
  ring

lemma high_scale (r t : ℝ) : high (q*r) (q*t)=q*high r t := by
  unfold high splice
  simp only [show 8*(q*r)=q*(8*r) by ring,mul_le_mul_iff_right₀ hq]
  split_ifs
  · rfl
  · rw [show 10*(q*r)=q*(10*r) by ring,show 2*(q*r)=q*(2*r) by ring,
      quadratic_scale hq]

lemma positivePart_scale (a r t : ℝ) : positivePart (q*a) (q*r) (q*t)=q*positivePart a r t := by
  unfold positivePart splice
  simp only [show 2*(q*a)=q*(2*a) by ring,mul_le_mul_iff_right₀ hq]
  split_ifs
  · exact low_scale hq a t
  · exact high_scale hq r t

lemma scalar_scale (a r t : ℝ) : scalar (q*a) (q*r) (q*t)=q*scalar a r t := by
  unfold scalar splice
  simp only [show q*t≤0 ↔ t≤0 by constructor <;> intro h <;> nlinarith only [hq,h]]
  split_ifs
  · rw [show -(q*t)=q*(-t) by ring,positivePart_scale hq]
    ring
  · exact positivePart_scale hq a r t

lemma taper_scale {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (hd : ∀ x y, dist (f x) (f y)=q*dist x y)
    (S : Set X) (r : ℝ) (x : X) : taper (f '' S) (q*r) (f x)=taper S r x := by
  unfold taper
  rw [Set.image_nonempty]
  split_ifs
  · rw [infDist_homothety f hq hd]
    congr 1
    exact mul_div_mul_left _ _ hq.ne'
  · rfl
end Increment
end PlanarL1

namespace PlanarL1.Columns.Model
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q)
include hq in
lemma scale_univ : (fun T : ℝ => q*T) '' Set.univ=Set.univ := by
  ext T
  simp only [mem_dilate_set q hq,Set.mem_univ]

namespace Point
lemma dist_band_eq {J I : Set ℝ} {r s : Fin (k+1)} (h : J=I)
    (x y : M.Point J r) (x' y' : M.Point I s)
    (hx : x.column=x'.column) (hX : x.height=x'.height)
    (hy : y.column=y'.column) (hY : y.height=y'.height) : dist x y=dist x' y' := by
  subst I
  exact Point.dist_coordinates x y x' y' hx hX hy hY
end Point
namespace Ambient
variable (A : Ambient M)
noncomputable def dilate : Ambient (M.dilate q hq) where
  root := A.root
  connected i := by
    rw [← scale_univ hq,M.dilate_activeGraph]
    exact A.connected i

noncomputable def scaleEquiv : M.Point Set.univ A.root ≃ (M.dilate q hq).Point Set.univ (A.dilate hq).root where
  toFun x := (A.dilate hq).point x.column (q*x.height)
  invFun x := A.point x.column (x.height/q)
  left_inv x := by cases x; simp only [point,mul_div_cancel_left₀ _ hq.ne']
  right_inv x := by cases x; simp only [point,mul_div_cancel₀ _ hq.ne']

lemma scaleEquiv_dist (x y : M.Point Set.univ A.root) :
    dist (A.scaleEquiv hq x) (A.scaleEquiv hq y)=q*dist x y := by
  rw [← Point.dist_band_eq (scale_univ hq) (x.dilate hq) (y.dilate hq)
    (A.scaleEquiv hq x) (A.scaleEquiv hq y) rfl rfl rfl rfl]
  exact x.dilate_dist hq y

lemma scaleEquiv_point (i : Fin (k+1)) (T : ℝ) :
    A.scaleEquiv hq (A.point i T)=(A.dilate hq).point i (q*T) := rfl

namespace History
variable {A} {c : ℝ}
noncomputable def dilate (H : History A c) : History (A.dilate hq) c where
  count := H.count
  radius j := q*H.radius j
  region j := A.scaleEquiv hq '' H.region j
  sign := H.sign
  positive j := mul_pos hq (H.positive j)
  separated i j hij := by
    rcases H.separated i j hij with h | h
    · left; nlinarith only [hq,h]
    · right; nlinarith only [hq,h]
end History
end Ambient
end PlanarL1.Columns.Model

namespace PlanarL1.Columns.Model.Field
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q) {J : Set ℝ} {L : ℝ≥0}

def coordinateScale (q : ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (q*z.1,q*z.2)

include hq in
lemma coordinateScale_dist (x y : ℝ×ℝ) :
    dist (coordinateScale q x) (coordinateScale q y)=q*dist x y := by
  simp only [coordinateScale,Prod.dist_eq,Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hq]
  rw [mul_max_of_nonneg _ _ hq.le]

lemma dilate_wall (F : M.Field J L) (a b : Fin (k+1)) :
    (F.dilate hq).wall a b=coordinateScale q '' F.wall a b := by
  ext z
  constructor
  · rintro (⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨i,j,H,hs,hi,hj,rfl⟩)
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value a U,U.val),Or.inl ⟨U,rfl⟩,by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value b U,U.val),Or.inr (Or.inl ⟨U,rfl⟩),by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
    · let U : J := ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩
      exact ⟨(F.value i U,U.val),Or.inr (Or.inr ⟨i,j,U,
        (M.dilate_mem_heights q hq).mp hs,hi,hj,rfl⟩),by
        simp only [coordinateScale,dilate,U,mul_div_cancel₀ _ hq.ne']⟩
  · rintro ⟨z,(⟨H,rfl⟩ | ⟨H,rfl⟩ | ⟨i,j,H,hs,hi,hj,rfl⟩),rfl⟩
    · refine Or.inl ⟨⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,?_⟩
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']
    · refine Or.inr (Or.inl ⟨⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,?_⟩)
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']
    · refine Or.inr (Or.inr ⟨i,j,⟨q*H.val,Set.mem_image_of_mem _ H.property⟩,
        Set.mem_image_of_mem _ hs,hi,hj,?_⟩)
      simp only [coordinateScale,dilate,mul_div_cancel_left₀ _ hq.ne']

lemma dilate_transverseValue (F : M.Field J L) (a b i : Fin (k+1))
    (H : (fun T => q*T) '' J) :
    (F.dilate hq).transverseValue a b i H=
      q*F.transverseValue a b i ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩ := by
  unfold transverseValue
  rw [dilate_wall hq]
  have he : ((F.dilate hq).value i H,H.val)=
      coordinateScale q (F.value i ⟨H.val/q,(mem_dilate_set q hq).mp H.property⟩,H.val/q) := by
    simp only [coordinateScale,dilate,mul_div_cancel₀ _ hq.ne']
  rw [he,PlanarL1.infDist_homothety _ hq (coordinateScale_dist hq)]
  ring
end PlanarL1.Columns.Model.Field

namespace PlanarL1.Columns.Model
open scoped NNReal
variable {k : ℕ} {M : Model (k+1)} {q : ℝ} (hq : 0<q) {A : Ambient M} {c : ℝ}
namespace Ambient.History
lemma dilate_field (H : History A c) {I : Set ℝ} (s : M.Field I 4)
    (a b : Fin (k+1)) (hc : 0<c) (hcr : c≤4) (i : Fin (k+1))
    (T : (fun U => q*U) '' I) :
    ((H.dilate hq).field (s.dilate hq) a b hc hcr).value i T=
      q*(H.field s a b hc hcr).value i ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩ := by
  classical
  let U : I := ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩
  have ht : ((s.dilate hq).transverse (by norm_num) a b).value i T=
      q*(s.transverse (by norm_num) a b).value i U := s.dilate_transverseValue hq a b i T
  have hw (j : Fin H.count) :
      Increment.taper ((A.scaleEquiv hq '' H.region j)ᶜ) (q*H.radius j)
        ((A.dilate hq).point i T.val)=Increment.taper (H.region j)ᶜ (H.radius j) (A.point i U.val) := by
    rw [← Equiv.image_compl]
    have he : (A.dilate hq).point i T.val=A.scaleEquiv hq (A.point i U.val) := by
      change (A.dilate hq).point i T.val=(A.dilate hq).point i (q*(T.val/q))
      rw [mul_div_cancel₀ _ hq.ne']
    rw [he]
    exact Increment.taper_scale hq (A.scaleEquiv hq) (A.scaleEquiv_dist hq) _ _ _
  change (∑ j : Fin H.count, Increment.signedDamped (H.sign j) (c*(q*H.radius j)) (q*H.radius j)
    (((s.dilate hq).transverse (by norm_num) a b).value i)
    (fun W => Increment.taper (A.scaleEquiv hq '' H.region j)ᶜ (q*H.radius j) ((A.dilate hq).point i W.val)) T)=
      q*∑ j : Fin H.count, Increment.signedDamped (H.sign j) (c*H.radius j) (H.radius j)
        ((s.transverse (by norm_num) a b).value i)
        (fun W => Increment.taper (H.region j)ᶜ (H.radius j) (A.point i W.val)) U
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold Increment.signedDamped Increment.damped
  simp only [ht,hw,show c*(q*H.radius j)=q*(c*H.radius j) by ring,Increment.scalar_scale hq]
  cases H.sign j <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring
end Ambient.History

namespace BData
lemma dilate_recorded (D : BData M) (H : A.History c) (hc : 0<c) (hcr : c≤4)
    (h : D.Recorded H hc hcr) : (D.dilate hq).Recorded (H.dilate hq) hc hcr := by
  cases D with
  | ordinary D => trivial
  | ordered D =>
    intro i T
    change q*D.auxiliary.value i ⟨T.val/q,(mem_dilate_set q hq).mp T.property⟩=
      ((H.dilate hq).field (D.base.dilate hq) D.lower D.upper hc hcr).value i T
    exact (congrArg (q*·) (h i _)).trans (H.dilate_field hq D.base D.lower D.upper hc hcr i T).symm
end BData

namespace BState.Histories
open MeasureTheory
variable {κ : ℝ} {lam : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {S : BState M κ lam Ω μ} {hc : 0<c} {hcr : c≤4} {t : ℝ}
noncomputable def dilate (H : BState.Histories A hc hcr S t) :
    BState.Histories (A.dilate hq) hc hcr (S.dilate hq) (q*t) where
  history a := (H.history a).dilate hq
  older a j := mul_le_mul_of_nonneg_left (H.older a j) hq.le
  recorded a := (S.chart a).dilate_recorded hq (H.history a) hc hcr (H.recorded a)
end BState.Histories
end PlanarL1.Columns.Model

end


section

namespace PlanarL1.Columns.Model
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {I J : Set ℝ} {r s : Fin n}
namespace Field
lemma ext_value {K : ℝ≥0} {F G : M.Field I K} (h : F.value=G.value) : F=G := by
  cases F
  cases G
  cases h
  rfl
end Field
namespace Point
/-- Changing the bookkeeping root does not change a geometric point. -/
def reRoot (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) : M.Point I s :=
  ⟨x.column,x.height,x.inBand,h.trans x.reachable⟩
@[simp] lemma reRoot_column (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).column=x.column := rfl
@[simp] lemma reRoot_height (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).height=x.height := rfl
@[simp] lemma reRoot_inverse (h : (M.activeGraph I).Reachable s r) (x : M.Point I r) :
    (x.reRoot h).reRoot h.symm=x := by cases x; rfl
@[simp] lemma dist_reRoot (h : (M.activeGraph I).Reachable s r) (x y : M.Point I r) :
    dist (x.reRoot h) (y.reRoot h)=dist x y :=
  dist_coordinates _ _ _ _ rfl rfl rfl rfl
lemma radialValue_reRoot (h : (M.activeGraph I).Reachable s r) (o : M.Point I r)
    (i : Fin n) (H : I) : (o.reRoot h).radialValue i H=o.radialValue i H := by
  by_cases hi : (M.activeGraph I).Reachable r i
  · have hs := h.trans hi
    simp only [radialValue,dite_eq_left hi,dite_eq_left hs]
    exact dist_coordinates _ _ _ _ rfl rfl rfl rfl
  · have hs : ¬(M.activeGraph I).Reachable s i := fun hs => hi (h.symm.trans hs)
    simp only [radialValue,dite_eq_right hi,dite_eq_right hs]
lemma radialField_reRoot (h : (M.activeGraph I).Reachable s r) (o : M.Point I r) :
    (o.reRoot h).radialField=o.radialField := by
  apply Field.ext_value
  funext i H
  exact radialValue_reRoot h o i H
end Point

namespace Field
variable {F : M.Field I 1} {ε : ℝ}
@[simp] lemma eval_reRoot (F : M.Field I 1) (h : (M.activeGraph I).Reachable s r)
    (x : M.Point I r) : F.eval (x.reRoot h)=F.eval x := rfl

def BandDescent.reRoot (h : (M.activeGraph I).Reachable s r) {x : M.Point I r}
    (D : F.BandDescent J x ε) : F.BandDescent J (x.reRoot h) ε where
  start_in := D.start_in
  target := D.target.reRoot h
  target_in := D.target_in
  path := D.path
  shortest := D.shortest
  lower := D.lower
  upper := D.upper
  drop := D.drop

lemma NoLowCircular.reRoot (h : (M.activeGraph I).Reachable s r)
    {x y : M.Point I r} {j : ℝ} (H : F.NoLowCircular x y J j) :
    F.NoLowCircular (x.reRoot h) (y.reRoot h) J j := by
  intro v b hv hs hn ht hd
  have hd' : dist x (v.reRoot h.symm)≤1 ∨ dist y (v.reRoot h.symm)≤1 := by
    have hx := Point.dist_coordinates (x.reRoot h) v x (v.reRoot h.symm) rfl rfl rfl rfl
    have hy := Point.dist_coordinates (y.reRoot h) v y (v.reRoot h.symm) rfl rfl rfl rfl
    simpa only [hx,hy] using hd
  exact H (v.reRoot h.symm) b hv hs hn ht hd'

lemma constant_no_descent (c ε : ℝ) (hε : ε < (1:ℝ)/100000) (x : M.Point I r) :
    ¬Nonempty ((constant M I c).BandDescent J x ε) := by
  rintro ⟨D⟩
  have hd := D.drop
  change c≤c-D.path.length x.height D.target.height+ε at hd
  linarith [D.lower]
end Field
namespace OrdinaryData
/-- Constant ordinary charts cannot survive the genuine descending-path test.
A surviving source is relocated to the bookkeeping root of the current band. -/
lemma source_of_descent (D : OrdinaryData M) {root : Fin n}
    (x : M.Point D.band root) (hx : D.Contains x.column x.height)
    {ε : ℝ} (hε : ε < (1:ℝ)/100000)
    (hd : Nonempty (D.comparison.BandDescent J x ε)) :
    ∃ o : M.Point D.band root, D.comparison=o.radialField := by
  cases ho : D.origin with
  | none =>
    have hh : ¬Nonempty (D.comparison.BandDescent J x ε) := by
      simpa only [comparison,ho] using Field.constant_no_descent (M := M) 0 ε hε x
    exact (hh hd).elim
  | some o =>
    have hr := x.reachable.trans (hx.2 o.1 o.2 ho).symm
    refine ⟨o.2.reRoot hr,?_⟩
    rw [Point.radialField_reRoot]
    simp only [comparison,ho]
end OrdinaryData
end PlanarL1.Columns.Model

end

end OAI
