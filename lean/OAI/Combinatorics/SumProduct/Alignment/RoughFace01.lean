import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughProduct03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma badProduct_zero_false {v : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z : ℝ}
    {d M : ℕ} {A : Fin v → ℤ} {P : (Fin (0+v) → ℝ) → G}
    {t : Fin 0 → ℤ} (hη : 0<η) : ¬badProduct Γ 0 v c₀ C₀ B η Z d M A P t := by
  rintro ⟨lo,hi,res,test,hside,hbox,hlip,hbound,hdisc⟩
  have he : nestedBox lo hi res A d M (∏ j,t j)=physicalResidueBox lo hi res d := by
    simp [nestedBox]
  rw [he,sub_self,norm_zero] at hdisc
  exact hη.not_ge hdisc

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma exceptionalProduct_succ_card {m v : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z : ℝ}
    {d M : ℕ} {A : Fin v → ℤ} {P : (Fin ((m+1)+v) → ℝ) → G}
    {S : Fin (m+1) → ℝ} {r : Fin (m+1) → ℤ} {L : ℤ} :
    (exceptionalProduct Γ (m+1) v c₀ C₀ B η Z d M A P S r L).card=
      (((times (S 0) (r 0) L).product (productTimes (Fin.tail S) (Fin.tail r) L)).filter
        (fun p=>badProduct Γ (m+1) v c₀ C₀ B η Z d M A P (consPair p))).card := by
  classical
  rw [exceptionalProduct,productTimes_succ,Finset.filter_image,
    Finset.card_image_of_injective _ (consPair_injective m)]

theorem source_product_decay (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin m → ℝ) (Z : ℕ→ℝ)
    (r : ℕ → Fin m → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(1+∑ j,S n j)^a) atTop atTop)
    (_ : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptionalProduct Γ m v c₀ C₀ B η (Z n) d (M n) A P (S n) (r n) (L n)).card:ℝ)/
        ((productTimes (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  induction m generalizing η with
  | zero =>
    intro ε hε
    filter_upwards [] with n
    intro A P hP
    have he : exceptionalProduct Γ 0 v c₀ C₀ B η (Z n) d (M n) A P (S n) (r n) (L n)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact badProduct_zero_false Γ hη (Finset.mem_filter.mp ht).2
    rw [he,Finset.card_empty,Nat.cast_zero,zero_div]
    exact hε
  | succ m ih =>
    intro ε hε
    have htail := ih (η:=η/2) (by positivity) (S:=fun n=>Fin.tail (S n))
      (r:=fun n=>Fin.tail (r n)) (fun j=>hS j.succ)
      (tail_domination S Z hS hZ) (fun n j=>hr n j.succ) (fun j=>hSL j.succ)
      (ε/3) (by positivity)
    have hfirst := firstBad_fiber_eventual c Γ hsk hΓ htop m v D d hd c₀ C₀ B (η/2)
      hc₀ hC₀ hB (by positivity) w M S Z r L hw hS hZ hMs hL hsm hWL hr hSL
      (ε/3) (by positivity)
    have htailnonempty := productTimes_nonempty_eventually (fun n=>Fin.tail (S n))
      (fun n=>Fin.tail (r n)) L hL (fun j=>hS j.succ) (fun j=>hSL j.succ)
    have htimepos := timeLength_tendsto (r:=fun n=>r n 0) hL (hS 0) (hSL 0)
    filter_upwards [htail,hfirst,htailnonempty,htimepos.eventually (eventually_gt_atTop 0)] with n htn hfn htnon htime
    intro A P hP
    have htpos : (0:ℝ)<(productTimes (Fin.tail (S n)) (Fin.tail (r n)) (L n)).card := by
      exact_mod_cast Finset.card_pos.mpr htnon
    have hspos : (0:ℝ)<(times (S n 0) (r n 0) (L n)).card := by
      rw [times_card _ _ _ (hL n)]
      exact htime
    have hf := product_exception_bound (times (S n 0) (r n 0) (L n))
      (productTimes (Fin.tail (S n)) (Fin.tail (r n)) (L n))
      (fun s t=>badProduct Γ m v c₀ C₀ B (η/2) (Z n) d (M n) A
        (fun y=>P (tailLift (s:ℝ) y)) t)
      (fun s t=>firstBad Γ m v c₀ C₀ B (η/2) (Z n) d (M n) A P s t)
      (fun s t=>badProduct Γ (m+1) v c₀ C₀ B η (Z n) d (M n) A P (consPair (s,t)))
      (ε/3) (ε/3)
      (fun s hs=>((div_lt_iff₀ htpos).mp
        (htn A (fun y=>P (tailLift (s:ℝ) y)) (tail_polynomial c P hP _))).le)
      (hfn A P hP)
      (fun s hs t ht h=>badProduct_succ_split Γ h)
    rw [exceptionalProduct_succ_card,card_productTimes_succ,Nat.cast_mul]
    apply (div_lt_iff₀ (mul_pos hspos htpos)).mpr
    calc
      _ ≤ (ε/3+ε/3)*(times (S n 0) (r n 0) (L n)).card*
        (productTimes (Fin.tail (S n)) (Fin.tail (r n)) (L n)).card := hf
      _ < ε*((times (S n 0) (r n 0) (L n)).card*
        (productTimes (Fin.tail (S n)) (Fin.tail (r n)) (L n)).card) := by
          nlinarith [mul_pos hspos htpos]

end RoughProductRemoval
end
end
 

section
 
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]

def badFace (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (d M : ℕ) (A : Fin v → ℤ) (P : (Fin (m+v) → ℝ) → G)
    (σ : (G⧸Γ) → (G⧸Γ)) (t : Fin m → ℤ) : Prop :=
  ∃ (lo hi : Fin v → ℝ) (res : Fin v → ℤ) (test : (G⧸Γ) → ℂ),
    (∀ i,c₀*Z≤hi i-lo i) ∧ (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (nestedBox lo hi res A d M (∏ j,t j))
      (fun x=>test (σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))-
    mean (nestedBox lo hi res A d M (∏ j,t j))
      (fun x=>test (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ))))))‖

def exceptionalFace (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (d M : ℕ) (A : Fin v → ℤ) (P : (Fin (m+v) → ℝ) → G)
    (σ : (G⧸Γ) → (G⧸Γ)) (S : Fin m → ℝ) (r : Fin m → ℤ) (L : ℤ) :
    Finset (Fin m → ℤ) := by
  classical
  exact (productTimes S r L).filter (badFace Γ m v c₀ C₀ B η Z d M A P σ)

end RoughFaceShift
end
end
 

section
 
noncomputable section
namespace RoughFaceShift
open ComparableBoxLeibman RoughSamplingWeights RoughAnalyticExtraction FinitePieceAverages
open scoped BigOperators

lemma rectMean_natShift {v : ℕ} {L : Fin v → ℕ} (hL : ∀ i,0<L i)
    (f : (Fin v → ℕ) → ℂ) (B : ℝ) (hB : 0<B) (hf : ∀ x,‖f x‖≤B)
    (h : Fin v → ℕ) :
    ‖rectMean v L (fun x=>f (x+h))-rectMean v L f‖≤
      B * ∑ i,2*(h i:ℝ)/(L i:ℝ) := by
  let g : (Fin v → ℕ) → ℂ := fun x=>(B:ℂ)⁻¹*f x
  have hg : ∀ x,‖g x‖≤1 := by
    intro x
    dsimp [g]
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB]
    exact (inv_mul_le_one₀ hB).mpr (hf x)
  have he : ∀ x,f x=(B:ℂ)*g x := by
    intro x
    dsimp [g]
    rw [← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast hB.ne'),one_mul]
  have hh := rectMean_shift v hL g hg h
  have h1 : rectMean v L (fun x=>f (x+h)) =
      (B:ℂ)*rectMean v L (fun x=>g (x+h)) := by
    rw [← rectMean_smul]
    congr 1
    funext x
    exact he _
  have h0 : rectMean v L f = (B:ℂ)*rectMean v L g := by
    rw [← rectMean_smul]
    congr 1
    exact funext he
  rw [h1,h0,← mul_sub,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hB]
  exact mul_le_mul_of_nonneg_left hh hB.le

lemma rectMean_intShift {v : ℕ} {L : Fin v → ℕ} (hL : ∀ i,0<L i)
    (f : (Fin v → ℤ) → ℂ) (B : ℝ) (hB : 0<B) (hf : ∀ x,‖f x‖≤B)
    (a h : Fin v → ℤ) :
    ‖rectMean v L (fun x=>f (fun i=>a i+(x i:ℤ)+h i))-
      rectMean v L (fun x=>f (fun i=>a i+(x i:ℤ)))‖≤
      B * ∑ i,2*|(h i:ℝ)|/(L i:ℝ) := by
  let hp : Fin v → ℕ := fun i=>(h i).toNat
  let hm : Fin v → ℕ := fun i=>(-h i).toNat
  let g : (Fin v → ℕ) → ℂ := fun x=>f (fun i=>a i+(x i:ℤ)-(hm i:ℤ))
  have hep : (fun x=>f (fun i=>a i+(x i:ℤ)+h i))=fun x=>g (x+hp) := by
    funext x
    congr 1
    ext i
    simp only [Pi.add_apply,Nat.cast_add]
    dsimp [hp,hm]
    omega
  have hem : (fun x=>f (fun i=>a i+(x i:ℤ)))=fun x=>g (x+hm) := by
    funext x
    congr 1
    ext i
    simp only [Pi.add_apply,Nat.cast_add]
    omega
  rw [hep,hem]
  have hgp := rectMean_natShift hL g B hB (fun x=>hf _) hp
  have hgm := rectMean_natShift hL g B hB (fun x=>hf _) hm
  have ht := (norm_sub_le_norm_sub_add_norm_sub
    (rectMean v L (fun x=>g (x+hp))) (rectMean v L g)
    (rectMean v L (fun x=>g (x+hm)))).trans
      (add_le_add hgp (by simpa only [norm_sub_rev] using hgm))
  have he : (∑ i,2*(hp i:ℝ)/(L i:ℝ))+(∑ i,2*(hm i:ℝ)/(L i:ℝ))=
      ∑ i,2*|(h i:ℝ)|/(L i:ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (hp i:ℝ)+(hm i:ℝ)=|(h i:ℝ)| := by
      have hi' : (hp i:ℤ)+(hm i:ℤ)=|h i| := by
        dsimp [hp,hm]
        by_cases hh : 0≤h i
        · rw [abs_of_nonneg hh]
          omega
        · rw [abs_of_neg (by omega : h i<0)]
          omega
      exact_mod_cast hi'
    rw [← add_div,← mul_add,hi]
  calc
    _ ≤ B*(∑ i,2*(hp i:ℝ)/(L i:ℝ))+B*(∑ i,2*(hm i:ℝ)/(L i:ℝ)) := ht
    _ = _ := by rw [← mul_add,he]

lemma halfOpenLength_lower (lo hi W : ℝ) (hW : 4≤W) (hside : W≤hi-lo) :
    W/4≤(integerLength lo ((⌈hi⌉:ℝ)-1):ℝ) := by
  have hh := integerLength_lower lo ((⌈hi⌉:ℝ)-1) (W/2) (by linarith) (by
    have := Int.le_ceil hi
    linarith)
  linarith

lemma boxMean_translation {v : ℕ} (lo hi : Fin v → ℝ) (a : Fin v → ℤ)
    (B W H : ℝ) (hB : 0<B) (hW : 4≤W) (hside : ∀ i,W≤hi i-lo i)
    (hH : 0≤H) (ha : ∀ i,|(a i:ℝ)|≤H)
    (f : (Fin v → ℤ) → ℂ) (hf : ∀ x,‖f x‖≤B) :
    ‖mean (boxIndices lo hi (fun _=>0) 1) (fun x=>f (x+a))-
      mean (boxIndices lo hi (fun _=>0) 1) f‖ ≤ 8*B*(v:ℝ)*H/W := by
  have hlen := fun i=>halfOpenLength_lower (lo i) (hi i) W hW (hside i)
  have hpos : ∀ i,0 < integerLength (lo i) ((⌈hi i⌉:ℝ)-1) := by
    intro i
    have : (0:ℝ)< integerLength (lo i) ((⌈hi i⌉:ℝ)-1) := lt_of_lt_of_le (by linarith) (hlen i)
    exact_mod_cast this
  simp only [mean_eq_expect,boxIndices_eq_halfOpen,halfOpenBox,integerBox_average]
  have hh := rectMean_intShift hpos f B hB hf (fun i=>⌈lo i⌉) a
  apply hh.trans
  have hterm : ∀ i,2*|(a i:ℝ)|/(integerLength (lo i) ((⌈hi i⌉:ℝ)-1):ℝ)≤8*H/W := by
    intro i
    have hL : (0:ℝ)< integerLength (lo i) ((⌈hi i⌉:ℝ)-1) := by exact_mod_cast hpos i
    apply (div_le_iff₀ hL).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : 0<W)).mpr
    have hnon : 0≤H*(integerLength (lo i) ((⌈hi i⌉:ℝ)-1)-W/4) :=
      mul_nonneg hH (sub_nonneg.mpr (hlen i))
    nlinarith [mul_nonneg (sub_nonneg.mpr (ha i)) (by linarith : 0≤W)]
  calc
    B * ∑ i,2*|(a i:ℝ)|/(integerLength (lo i) ((⌈hi i⌉:ℝ)-1):ℝ)
      ≤ B * ∑ i : Fin v,8*H/W := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _=>hterm i)) hB.le
    _ = _ := by simp; ring

lemma residueMean_translation {v : ℕ} (lo hi : Fin v → ℝ) (u a : Fin v → ℤ)
    (d : ℕ) (hd : 0<d) (B W H : ℝ) (hB : 0<B) (hW : 4*(d:ℝ)≤W)
    (hside : ∀ i,W≤hi i-lo i) (hH : 0≤H)
    (ha : ∀ i,(d:ℤ)∣a i ∧ |(a i:ℝ)|≤H)
    (f : (Fin v → ℤ) → ℂ) (hf : ∀ x,‖f x‖≤B) :
    ‖mean (physicalResidueBox lo hi u d) (fun x=>f (x+a))-
      mean (physicalResidueBox lo hi u d) f‖≤8*B*(v:ℝ)*H/W := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  choose k hk using fun i=>(ha i).1
  have hkbound : ∀ i,|(k i:ℝ)|≤H/(d:ℝ) := by
    intro i
    apply (le_div_iff₀ hd').mpr
    have hh := (ha i).2
    rw [hk i,Int.cast_mul,Int.cast_natCast,abs_mul,abs_of_pos hd'] at hh
    nlinarith
  let lo' := rescaledEndpoint lo u d
  let hi' := rescaledEndpoint hi u d
  have hside' : ∀ i,W/(d:ℝ)≤hi' i-lo' i := by
    intro i
    dsimp [lo',hi',rescaledEndpoint]
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hd'.le
    linarith [hside i]
  have hbound := boxMean_translation lo' hi' k B (W/(d:ℝ)) (H/(d:ℝ)) hB
    ((le_div_iff₀ hd').mpr hW) hside' (div_nonneg hH hd'.le) hkbound
    (fun y=>f (integerAffine u d y)) (fun y=>hf _)
  have he : (fun y=>f (integerAffine u d y+a))=
      fun y=>f (integerAffine u d (y+k)) := by
    funext y
    congr 1
    ext i
    dsimp [integerAffine]
    simp only [hk i]
    ring
  rw [residue_mean lo hi u d hd,residue_mean lo hi u d hd,he]
  apply hbound.trans_eq
  have hW' : W≠0 := ne_of_gt (lt_of_lt_of_le (by positivity) hW)
  field_simp

end RoughFaceShift

end
end

end OAI
