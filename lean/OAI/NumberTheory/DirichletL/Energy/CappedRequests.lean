import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
import OAI.NumberTheory.DirichletL.Energy.SourceCapSchedule

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyCappedRequests
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergySourceCapSchedule

def requestLength (M B L:ℝ):ℝ:=max L (2*M+B+2)+1

lemma request_bounds (M B L:ℝ)(hM:0≤M)(hB:0≤B)(_hL:0≤L):
    0≤requestLength M B L ∧ L≤requestLength M B L ∧ M≤requestLength M B L:=by
  have hh:=le_max_left L (2*M+B+2)
  have hg:=le_max_right L (2*M+B+2)
  unfold requestLength
  constructor
  · linarith
  constructor <;> linarith

lemma actual_contours (M B L parent rho d:ℝ)(hM:0≤M)(_hB:0≤B)
    (hp:parent≤M)(hr:rho≤M)(hd:d≤1):
    max (max L (parent+B+2*d)+1) (parent+B+rho/100)≤requestLength M B L:=by
  have hmax:max L (parent+B+2*d)≤max L (2*M+B+2):=by
    apply max_le_max_left
    linarith
  have hh:=le_max_right L (2*M+B+2)
  unfold requestLength
  apply max_le <;> linarith

lemma doubled_request (M B L e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)(he:e≤1):
    2*requestLength M B L+e≤step M B L:=by
  have hh:max L (2*M+B+2)≤L+2*M+B+2:=by
    apply max_le <;> linarith
  unfold requestLength step
  linarith

lemma previous_admits (M B L ε parent e:ℝ)(hM:0≤M)(hB:0≤B)
    (hp:parent≤M)(he:e≤1)(k:ℕ)(hk:k<count M ε):
    2*max (requestLength M B (lengthAt M B L ε (k+1))) parent+e≤lengthAt M B L ε k:=by
  have hL:=range_nonneg M B L hM hB (remaining M ε (k+1))
  change 0≤lengthAt M B L ε (k+1) at hL
  have hreq:=request_bounds M B (lengthAt M B L ε (k+1)) hM hB hL
  rw [max_eq_left (hp.trans hreq.2.2),child_length M B L ε k hk]
  exact doubled_request M B _ e hM hB hL he

lemma request_le_final (M B L ε:ℝ)(hM:0≤M)(hB:0≤B)(k:ℕ)(hk:k<count M ε):
    requestLength M B (lengthAt M B L ε (k+1))≤range M B L (count M ε):=by
  have hh:=previous_admits M B L ε M 0 hM hB le_rfl (by norm_num) k hk
  have hl:=range_nonneg M B L hM hB (remaining M ε (k+1))
  have hr:0≤requestLength M B (lengthAt M B L ε (k+1)):=
    (request_bounds M B _ hM hB hl).1
  have hprev:lengthAt M B L ε k≤range M B L (count M ε):=
    range_mono M B L hM hB (Nat.sub_le _ _)
  have hmax:=le_max_left (requestLength M B (lengthAt M B L ε (k+1))) M
  linarith

lemma parent_drop (M B ε:ℝ)(hε:0<ε)(k:ℕ):
    bandWidth M B ε (k+1)-amplification ε/2≤bandWidth M B ε k:=
  actual_child_band M B ε _ _ hε k le_rfl le_rfl

lemma band_positive (M B ε:ℝ)(hM:0<M)(hB:0≤B)(hε:0<ε)(k:ℕ):
    0<bandWidth M B ε k:=by
  have hh:=bounds M B 0 ε hM.le hB (by norm_num) hε
  have hr:=hh.2.2.2.1
  have hs:=hh.1
  unfold bandWidth width
  exact lt_min hM (by positivity)

end SevenEighths.CenteredMomentEnergyCappedRequests

end

end OAI
