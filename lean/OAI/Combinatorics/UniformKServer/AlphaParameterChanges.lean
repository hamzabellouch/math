import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveAlpha

namespace OAI

                                            
section

/-! Prepared logarithmic parameter changes. All bounds concern the actual
 improper primitives, with constants uniform at vanishing side mass. -/
noncomputable section
namespace UniformKServer.AlphaParameterChanges
open Finset UniformKServer.AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

def piece (p : Config ι) (B a : ι → ℝ) : ι → ℝ :=
  DomainTransport.extend p.active (fun i =>
    ProportionParameters.component p.param (fun j => B j) i (a i))

theorem sum_piece (p : Config ι) (B a : ι → ℝ) : (∑ i, piece p B a i)=potential p B a := by
  exact DomainTransport.extend_sum _ _

omit [Fintype ι] in
theorem piece_outside (p : Config ι) (B a : ι → ℝ) (i : ι) (hi : i ∉ p.active) :
    piece p B a i=0 := DomainTransport.extend_supported _ _ _ hi

omit [Fintype ι] in
theorem piece_inside (p : Config ι) (B a : ι → ℝ) (i : p.active) :
    piece p B a i=ProportionParameters.component p.param (fun j => B j) i (a i) :=
  DomainTransport.extend_apply _ _ _

/-- An ordinary coordinate costs only its prepared input. -/
theorem regular_piece {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) (i : p.active)
    (he : ProportionParameters.component p.param (fun j => B j) i (a i)=
      AlphaTracker.regularG p.param.h (fun j => B j) p.param.ell p.param.ct p.param.C i (a i))
    (hh : 1 ≤ p.param.h i) : |piece p B a i| ≤ 4*scale p*B i := by
  rw [piece_inside,he]
  have h := AlphaBounds.regular_component hh (ha i) (scale p)
    (∑ j : p.active, B j) ((1+ProportionParameters.eta p.param i)*B i)
  rw [DomainTransport.sum_restrict hs,abs_of_nonneg (scale_nonneg hp),
    abs_of_nonneg (sum_nonneg fun j _ => hB j),
    abs_of_nonneg (mul_nonneg (by linarith [ProportionParameters.eta_nonneg hp.2 i]) (hB i))] at h
  have hm := mul_le_mul_of_nonneg_right (hp.2.2.2.2.1 i) (hB i)
  have heq : AlphaTracker.regularG p.param.h (fun j => B j) p.param.ell p.param.ct p.param.C i (a i)=
      LogPrimitive.primitive (Denominators.regular (p.param.h i)) 0 (scale p)
        (∑ j, B j) ((1+ProportionParameters.eta p.param i)*B i) (a i) := by
    unfold AlphaTracker.regularG scale ProportionParameters.eta
    rw [DomainTransport.sum_restrict hs]
  rw [heq]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left (hf i) (scale_nonneg hp),
    mul_le_mul_of_nonneg_left hm (scale_nonneg hp)])

theorem prepared_two {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hf : ∀ i, (∑ j, B j)*a i ≤ (1+eta p i)*B i) :
    ∀ i, (∑ j, B j)*a i ≤ 2*B i := by
  intro i
  have he : eta p i ≤ 1 := by
    by_cases hi : i ∈ p.active
    · simpa only [eta,DomainTransport.extend,hi,dite_true] using hp.2.2.2.2.1 ⟨i,hi⟩
    · rw [eta,DomainTransport.extend_supported _ _ i hi]; norm_num
  exact (hf i).trans (mul_le_mul_of_nonneg_right (by linarith) (hB i))

/-- Sum of prepared side constraints, without division by total input. -/
theorem prepared_side (B a : ι → ℝ) (ha : ∑ i, a i=1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) (o : ι) :
    (∑ j, B j)*(1-a o) ≤ 2*((∑ j, B j)-B o) := by
  have h := sum_le_sum (s:=univ.erase o) (fun i _ => hf i)
  rw [←mul_sum,←mul_sum,sum_erase_eq_sub (mem_univ o),
    sum_erase_eq_sub (mem_univ o),ha] at h
  exact h

/-- A regular epoch, including additions/removals, charges only the coordinates
 whose parameter piece changes. The indicator is later identified with held
 size refreshes; no degree factor appears. -/
theorem regular_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (hep : p.param.kind=.regular) (heq : q.param.kind=.regular)
    (B a : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hsp : DomainTransport.Supported p.active B) (hsq : DomainTransport.Supported q.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i)
    (changed : ι → Prop) [DecidablePred changed]
    (same : ∀ i, ¬changed i → piece p B a i=piece q B a i) :
    |potential q B a-potential p B a| ≤
      4*(scale p+scale q)*(∑ i, if changed i then B i else 0) := by
  have bound (r : Config ι) (hr : valid r) (he : r.param.kind=.regular)
      (hs : DomainTransport.Supported r.active B) (i : ι) :
      |piece r B a i| ≤ 4*scale r*B i := by
    by_cases hi : i ∈ r.active
    · apply regular_piece hr B a hB hs ha hf ⟨i,hi⟩
      · simp [ProportionParameters.component,he]
      · have hk := hr.2.2.2.2.2
        simp only [he] at hk
        exact hk.1 ⟨i,hi⟩
    · rw [piece_outside _ _ _ _ hi,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hr)) (hB i)
  rw [←sum_piece,←sum_piece,←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hi : changed i
  · rw [ite_eq_left hi]
    exact (abs_sub _ _).trans (by nlinarith [bound p hp hep hsp i,bound q hq heq hsq i])
  · rw [ite_eq_right hi,same i hi,sub_self,abs_zero,mul_zero]

/-- Whole marked potential on a prepared state. In particular only side input
 and u times total input are charged when the distinguished parameter changes. -/
theorem marked_prepared {p : Config ι} (hp : valid p) (o : p.active) (u : ℝ)
    (he : p.param.kind=.marked o u) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) (hasum : ∑ i, a i=1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) :
    |potential p B a| ≤ 13*scale p*((∑ i, B i)-B o)+
      3*scale p*(p.param.ct/p.param.ell)*u*(∑ i, B i) := by
  have hk := hp.2.2.2.2.2
  simp only [he] at hk
  have hS : 0 ≤ ∑ i, B i := sum_nonneg fun i _ => hB i
  have hBo : B o ≤ ∑ i, B i := single_le_sum (fun j _ => hB j) (mem_univ o.val)
  have hηo : ProportionParameters.eta p.param o=(p.param.ct/p.param.ell)*u := by
    unfold ProportionParameters.eta
    rw [hk.2.2.1]; ring
  have hmark := AlphaStability.marked_prepared_component (E:=1) hk.1 hk.2.1 (ha o) hS (hB o) hBo
    (ProportionParameters.eta_nonneg hp.2 o) (le_of_eq hηo) (by convert prepared_side B a hasum hf o using 1; norm_num) (scale p)
  rw [abs_of_nonneg (scale_nonneg hp)] at hmark
  have hpo : piece p B a o=LogPrimitive.primitive (Denominators.marked u) 1 (scale p)
      (∑ i, B i) ((1+ProportionParameters.eta p.param o)*B o) (a o) := by
    rw [piece_inside]
    unfold ProportionParameters.component
    rw [he]
    unfold AlphaTracker.markedG AlphaTracker.markedF
    simp only [ite_true]
    rw [DomainTransport.sum_restrict hs]
    rfl
  have hreg (i : ι) (hi : i ≠ o.val) : |piece p B a i| ≤ 4*scale p*B i := by
    by_cases hip : i ∈ p.active
    · have hio : (⟨i,hip⟩ : p.active) ≠ o := by intro h; exact hi (congrArg Subtype.val h)
      apply regular_piece hp B a hB hs ha hf ⟨i,hip⟩
      · unfold ProportionParameters.component
        rw [he]
        unfold AlphaTracker.markedG AlphaTracker.markedF AlphaTracker.regularG
        simp only [ite_eq_right hio]
      · exact hk.2.2.2.1 _ hio
    · rw [piece_outside _ _ _ _ hip,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hp)) (hB i)
  have h := sum_le_sum (s:=univ.erase o.val) (fun i hi => hreg i (mem_erase.mp hi).1)
  rw [←mul_sum] at h
  rw [←hpo] at hmark
  calc
    _ = |(∑ i ∈ univ.erase o.val, piece p B a i)+piece p B a o| := by
      rw [sum_erase_add _ _ (mem_univ o.val),sum_piece]
    _ ≤ (∑ i ∈ univ.erase o.val, |piece p B a i|)+|piece p B a o| :=
      (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ 4*scale p*(∑ i ∈ univ.erase o.val, B i)+
        3*scale p*((2+1)*((∑ i, B i)-B o)+(p.param.ct/p.param.ell)*u*(∑ i, B i)) :=
      add_le_add h hmark
    _ = _ := by rw [sum_erase_eq_sub (mem_univ o.val)]; ring

/-- The distinguished summand does not move when its held ratio is unchanged.
Only regular side summands remain in a size-refresh charge. -/
theorem marked_sparse_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (op : p.active) (oq : q.active) (u : ℝ)
    (hep : p.param.kind=.marked op u) (heq : q.param.kind=.marked oq u)
    (ho : op.val=oq.val) (B a : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hsp : DomainTransport.Supported p.active B) (hsq : DomainTransport.Supported q.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i)
    (changed : ι → Prop) [DecidablePred changed]
    (same : ∀ i, ¬changed i → piece p B a i=piece q B a i)
    (mark : ¬changed op.val) :
    |potential q B a-potential p B a| ≤
      4*(scale p+scale q)*(∑ i, if changed i then B i else 0) := by
  have bound (r : Config ι) (hr : valid r) (o : r.active)
      (he : r.param.kind=.marked o u) (hs : DomainTransport.Supported r.active B)
      (i : ι) (hio : i ≠ o.val) : |piece r B a i| ≤ 4*scale r*B i := by
    by_cases hi : i ∈ r.active
    · have hne : (⟨i,hi⟩ : r.active) ≠ o := by
        intro h; exact hio (congrArg Subtype.val h)
      apply regular_piece hr B a hB hs ha hf ⟨i,hi⟩
      · unfold ProportionParameters.component
        rw [he]
        unfold AlphaTracker.markedG AlphaTracker.markedF AlphaTracker.regularG
        simp only [ite_eq_right hne]
      · have hk := hr.2.2.2.2.2
        simp only [he] at hk
        exact hk.2.2.2.1 _ hne
    · rw [piece_outside _ _ _ _ hi,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (scale_nonneg hr)) (hB i)
  rw [←sum_piece,←sum_piece,←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hi : changed i
  · rw [ite_eq_left hi]
    have hio : i ≠ op.val := by rintro rfl; exact mark hi
    have hio' : i ≠ oq.val := by simpa only [←ho] using hio
    have hpbound := bound p hp op hep hsp i hio
    have hqbound := bound q hq oq heq hsq i hio'
    exact (abs_sub _ _).trans (by nlinarith)
  · rw [ite_eq_right hi,same i hi,sub_self,abs_zero,mul_zero]

omit [Fintype ι] in
theorem singleton_potential {p : Config ι} (o : p.active)
    (he : p.param.kind=.singleton o) (B a : ι → ℝ) : potential p B a=0 := by
  simp [potential,ProportionParameters.potential,ProportionParameters.component,he]

end UniformKServer.AlphaParameterChanges

end


end

end OAI
