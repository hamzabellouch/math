import OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters
import OAI.NumberTheory.DirichletL.Moments.LiveCapacity

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

def amplification (ε:ℝ):ℝ := min 1 (ε/16000)
def count (M ε:ℝ):ℕ := depth M (amplification ε)
def scale (M B ε:ℝ):ℝ := (count M ε:ℝ)+M+10*B+30
def reserve (M B ε:ℝ):ℝ :=
  min (amplification ε/100) (ε/(1000000*scale M B ε))
def mesh (M B κ ε:ℝ):ℝ := reserve M B ε/(κ+1)
def width (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε/16+(k:ℝ)*amplification ε/2
def loss (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε+64*(k:ℝ)*reserve M B ε

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0<reserve M B ε ∧ 0<mesh M B κ ε ∧ mesh M B κ ε≤reserve M B ε ∧
    κ*mesh M B κ ε≤reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0<reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤scale M B ε:=by unfold scale;linarith
  have h1L:1≤scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0<mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma reserve_cost (M B ε c:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)
    (hc:c≤scale M B ε):c*reserve M B ε≤ε/1000000:=by
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hr:0<reserve M B ε:=lt_min (by positivity) (by positivity)
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hh:=mul_le_mul_of_nonneg_right hc hr.le
  nlinarith

theorem one_time_losses (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (df es d theta other A:ℝ)(hdf:df≤reserve M B ε)(hes:es≤reserve M B ε)
    (hd:d≤reserve M B ε)(ht:theta≤reserve M B ε)(ho:other≤reserve M B ε)
    (he0:0≤es)(hA:A≤M):
    exceptional (amplification ε) df es d B theta≤ε/1000 ∧
      diagonal (amplification ε) d other es A≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hs:=hb.2.2.1
  have hr:=hb.2.2.2.1
  have hx:=reserve_cost M B ε (10*B+7) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have hy:=reserve_cost M B ε (M+2) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have htheta:=mul_le_mul_of_nonneg_left ht (show 0≤2*(5*B+1) by positivity)
  have hmul:es*A≤reserve M B ε*M:=
    (mul_le_mul_of_nonneg_left hA he0).trans (mul_le_mul_of_nonneg_right hes hM)
  constructor
  · unfold exceptional
    nlinarith
  · unfold diagonal
    nlinarith

lemma mesh_lt_prime_width (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    mesh M B κ ε<amplification ε/6:=by
  have h:=bounds M B κ ε hM hB hκ hε
  have hp:=h.1
  have hm:=h.2.2.2.2.2.1
  have hr:=h.2.2.2.2.2.2.2.1
  linarith

lemma width_zero (M B ε:ℝ):width M B ε 0=reserve M B ε/16:=by simp [width]
lemma loss_zero (M B ε:ℝ):loss M B ε 0=reserve M B ε:=by simp [loss]
lemma width_succ (M B ε:ℝ)(k:ℕ):
    width M B ε (k+1)-amplification ε/2=width M B ε k:=by
  simp only [width,Nat.cast_add,Nat.cast_one]
  ring
lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma child_band (M B ε parent child:ℝ)(k:ℕ)
    (hp:parent≤width M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤width M B ε k:=by
  rw [←width_succ M B ε k]
  linarith

lemma loss_le_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤count M ε):loss M B ε k≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hk':(k:ℝ)≤(count M ε:ℝ):=by exact_mod_cast hk
  apply le_trans _ hb.2.2.2.2.2.2.2.2.2
  unfold loss
  gcongr

lemma next_paid_loss (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other:ℝ)
    (her:er≤reserve M B ε)(hd:d≤reserve M B ε)(he:e≤reserve M B ε)
    (hd1:d1≤reserve M B ε)(hd2:d2≤reserve M B ε)(ht:theta≤reserve M B ε)
    (ho:other≤50*reserve M B ε):
    loss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+other≤
      loss M B ε (k+1):=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hm:=hb.2.2.2.2.2.2.1
  rw [loss_succ]
  unfold edge
  linarith

theorem actual_removal_path {ι:Type*}[DecidableEq ι]
    (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0<κ)(hε:0<ε)
    (n:ℕ)(J:Fin n→Finset ι)(w:Fin n→ι→ℝ)(x y state:Fin n→ℝ)
    (hw:∀k,∀i∈J k,0≤w k i)(hm:∀k,∀i∈J k,w k i≤mesh M B κ ε):
    ∃R:Fin n→Finset ι,(∀k,R k⊆J k) ∧
      (∀k,R k=J k ∨ x k+y k+6*κ*(∑i∈J k\R k,w k i)≤state k) ∧
      (∑k,κ*(∑i∈R k,w k i))≤
        (∑k,CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6)+
          (n:ℝ)*reserve M B ε:=by
  have hb:=bounds M B κ ε hM hB hκ.le hε
  have hmesh:=hb.2.2.2.2.1
  have hcost:=hb.2.2.2.2.2.2.1
  choose R hR hcap hpay using fun k=>CenteredMomentLiveCapacity.removal_excess_cost
    (J k) (w k) (x k) (y k) (state k) κ (mesh M B κ ε) hκ hmesh.le (hw k) (hm k)
  refine ⟨R,hR,hcap,?_⟩
  calc
    _≤∑k,(CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6+
        reserve M B ε):=Finset.sum_le_sum (fun k _=>(hpay k).trans (by linarith))
    _=_:=by rw [Finset.sum_add_distrib];simp

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI
