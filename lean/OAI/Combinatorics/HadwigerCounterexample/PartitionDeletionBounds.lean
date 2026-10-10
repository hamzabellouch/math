import OAI.Combinatorics.HadwigerCounterexample.WeightedPartitions
import OAI.Combinatorics.HadwigerCounterexample.UltrafilterRates

namespace OAI

/-! # Partition Deletion Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Filter Finset

variable {A B : Type} [Fintype A] {w : Wgt A}

/-- power lost on further restriction: measure removed at most error and
including normalization does not hurt the lower bound. -/
theorem joint_trim (hw : IsLaw w) (Q : A→Prop) (hq : 0<pr w Q)
    (P : A×A→Prop) :
    pr (pairW w w) P - 2*pr w (fun x=>¬Q x) ≤ pr (pairW (onW w Q) (onW w Q)) P := by
  classical
  let v:=pairW w w; let u:= onW w Q; let Z (x : A×A) := Q x.1 ∧ Q x.2
  have hv := pairW_law hw hw
  have h1 : pr v (fun x=>¬Z x) ≤ 2*pr w (fun x=>¬Q x) := by
    let M (x : A×A) := ¬Q x.1; let T (x : A×A) := ¬Q x.2
    have hM : pr v M = pr w (fun x=>¬Q x) := by
      have hh := pairW_pr w w (fun x=>¬Q x) (fun _=>True)
      simpa only [and_true,pr_true,hw.total,mul_one] using hh
    have hT : pr v T = pr w (fun x=>¬Q x) := by
      have hh := pairW_pr w w (fun _=>True) (fun x=>¬Q x)
      simpa only [true_and,pr_true,hw.total,one_mul] using hh
    have hm x : ¬Z x → M x ∨ T x := by unfold M Z T; tauto
    exact ((pr_mono hv.nz hm).trans (pr_or_le hv.nz)).trans_eq
      (by rw [hM,hT,two_mul])
  have h2 :
      pr v (fun x=> P x∧Z x) ≤ pr (pairW u u) P := by
    have hh (i) (hi : Q i) : w i ≤ u i := by
      unfold u; rw [onW_val,ind_one hi,mul_one]
      exact (le_div_iff₀ hq).mpr ((mul_le_mul_of_nonneg_left
        ((pr_le_tot hw.nz).trans hw.total.le) (hw.nz _)).trans_eq (mul_one _))
    unfold pr avg
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only
    by_cases hi : P i∧Z i
    · rw [ind_one hi,ind_one hi.1,mul_one,mul_one]
      exact mul_le_mul (hh _ hi.2.1) (hh _ hi.2.2) (hw.nz _) ((on_law hw.nz hq).nz _)
    rw [ind_zero hi,mul_zero]
    have huv : IsLaw u:=on_law hw.nz hq
    exact mul_nonneg ((pairW_law huv huv).nz _) (ind_nonneg _)
  exact (sub_le_sub_left h1 _).trans ((pr_shield hv.nz P Z).trans h2)

/-- Compose several restrictions starting from union T.
P marks on prior union. T restrict -> P -> V union subset of P in T;
user-given skip bound in absolute w. -/
theorem equity_trim (hw : ∀ x,0≤w x) (T V : A→Prop) (P : A→Prop)
    (hf : ∀ x,V x → T x∧P x)
    (hT : 0<pr w T) (hP : 0<pr (onW w T) P)
    {δ : ℝ} (hδ : pr w (fun x=>T x ∧ P x ∧ ¬V x) ≤ δ) :
    let W := onW (onW w T) P; let z := pr w T*pr (onW w T) P
    z-δ ≤ pr w V ∧
      (0<pr w V →
         ∀ Q : A×A→Prop,
          pr (pairW W W) Q-2*(δ/z) ≤ pr (pairW (onW w V) (onW w V)) Q) := by
  classical
  let B (x : A) := T x∧P x
  let W := onW w B
  have hz : pr w T*pr (onW w T) P=pr w B :=
    (pr_of_on hw T P).symm
  have hB := hz ▸ mul_pos hT hP
  have hh : pr w B ≤ pr w V+δ := by
    let R x := T x∧P x∧¬V x
    have he x : B x → V x ∨ R x := by unfold B R; tauto
    exact ((pr_mono hw he).trans (pr_or_le hw)).trans (add_le_add_right hδ _)
  dsimp only
  rw [on_both w T P hw hT hP,hz]
  refine ⟨by linarith only [hh],fun hv Q=>?_⟩
  have ht : (fun x=> B x∧V x) = V := by ext x; exact ⟨And.right, fun h=>⟨hf x h,h⟩⟩
  have hu : pr W V=pr w V / pr w B := by unfold W; rw [pr_on,ht]
  have hW : 0<pr W V := hu ▸ div_pos hv hB
  have h1 : onW W V=onW w V := by unfold W; rw [on_both w B V hw hB hW,ht]
  have h2 : pr W (fun x=>¬ V x)≤ δ/pr w B := by
    unfold W; rw [pr_on]
    refine div_le_div_of_nonneg_right ?_ hB.le
    unfold B; simpa only [and_assoc] using hδ
  rw [← h1]
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤2 by norm_num)) _).trans
    (joint_trim (on_law hw hB) V hW Q)

set_option maxHeartbeats 800000 in
theorem vigor_trim {l : Filter ℕ} (z : ℕ→ℝ) (hz : Tendsto z l atTop)
    {A : ℕ→Type} [∀ i,Fintype (A i)]
    (w : ∀ i,Wgt (A i)) (hw : ∀ᶠ i in l,∀ x,0 ≤ w i x)
    (T V P : ∀ i,A i→Prop) {δ : ℕ→ℝ} (hδ : ExpSmall l z δ)
    (hT : warm l z (fun i=>pr (w i) (T i)))
    (hP : warm l z (fun i=>pr (onW (w i) (T i)) (P i)))
    (hf : ∀ᶠ i in l,(∀ x,V i x → T i x ∧ P i x) ∧
       pr (w i) (fun x=>T i x∧ P i x∧¬V i x)≤δ i) :
    warm l z (fun i=>pr (w i) (V i)) ∧ ∃ d : ℕ→ℝ, ExpSmall l z d ∧
      ∀ᶠ i in l, let W:=onW (onW (w i) (T i)) (P i); let X := onW (w i) (V i);
        ∀ Q : A i×A i→Prop, pr (pairW W W) Q - d i ≤ pr (pairW X X) Q := by
  classical
  let c i:=pr (w i) (T i)*pr (onW (w i) (T i)) (P i)
  have hc : warm l z c := hT.mul hP
  let d i:= 2*(δ i / c i)
  have hd : ExpSmall l z d := by
    have hh := (hδ.mul hc.inv_cap).mul (expO_const hz 2)
    unfold d
    rw [show (fun i=>2*(δ i/c i))=(fun i=>δ i*(c i)⁻¹*2) from funext (fun i=>by rw [div_eq_mul_inv,mul_comm])]
    exact hh
  have he :
      ∀ᶠ i in l,c i-δ i≤ pr (w i) (V i) ∧ (0< pr (w i) (V i) →
        ∀ Q:A i × A i→Prop, let W:=onW (onW (w i) (T i)) (P i); let X:=onW (w i) (V i)
        pr (pairW W W) Q-d i≤pr (pairW X X) Q) := by
    filter_upwards [hw,hT.positive,hP.positive,hf] with i hi ht hv hf
    exact equity_trim hi _ _ _ hf.1 ht hv hf.2
  have hV := (hc.survive hz hδ).mono (he.mono (fun i hi=> hi.1))
  exact ⟨hV,d,hd,(he.and hV.positive).mono fun i ⟨hi,hv⟩=>hi.2 hv⟩
end HadwigerCounterexample

end

end OAI
