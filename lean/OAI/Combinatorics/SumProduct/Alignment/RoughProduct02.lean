import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughProduct01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RoughScales RoughSourceExceptional Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def consPair {m : ℕ} (p : ℤ × (Fin m → ℤ)) : Fin (m+1) → ℤ := Fin.cons p.1 p.2

lemma consPair_injective (m : ℕ) :
    Function.Injective (consPair (m:=m)) := by
  intro p q h
  apply Prod.ext
  · have h0:=congrFun h 0
    simpa only [consPair,Fin.cons_zero] using h0
  · funext i
    have hi:=congrFun h i.succ
    simpa only [consPair,Fin.cons_succ] using hi

lemma productTimes_succ {m : ℕ} (S : Fin (m+1) → ℝ) (r : Fin (m+1) → ℤ) (L : ℤ) :
    productTimes S r L =
      ((times (S 0) (r 0) L).product (productTimes (Fin.tail S) (Fin.tail r) L)).image
        consPair := by
  classical
  ext t
  simp only [productTimes,Fintype.mem_piFinset,Finset.mem_image,Finset.product_eq_sprod,Finset.mem_product]
  constructor
  · intro ht
    refine ⟨⟨t 0,Fin.tail t⟩,⟨ht 0,fun j=>ht j.succ⟩,?_⟩
    exact Fin.cons_self_tail t
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact Fin.forall_fin_succ.mpr ⟨ha,hb⟩

lemma card_productTimes_succ {m : ℕ} (S : Fin (m+1) → ℝ) (r : Fin (m+1) → ℤ) (L : ℤ) :
    (productTimes S r L).card =
      (times (S 0) (r 0) L).card*(productTimes (Fin.tail S) (Fin.tail r) L).card := by
  classical
  rw [productTimes_succ,Finset.card_image_of_injective _ (consPair_injective m),Finset.product_eq_sprod,Finset.card_product]

lemma filter_card_product_left {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (E : α → β → Prop) :
    (((S.product T).filter (fun p=>E p.1 p.2)).card) = ∑ a∈S,(T.filter (E a)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]

lemma filter_card_product_right {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (E : α → β → Prop) :
    letI := Classical.propDecidable
    (((S.product T).filter (fun p=>E p.1 p.2)).card) = ∑ b∈T,(S.filter (fun a=>E a b)).card := by
  classical
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  exact Finset.sum_comm

 
theorem product_exception_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (E F H : α → β → Prop)
    (a b : ℝ)
    (hE : ∀ x∈S,(((T.filter (E x)).card:ℕ):ℝ)≤a*T.card)
    (hF : ∀ y∈T,(((S.filter (fun x=>F x y)).card:ℕ):ℝ)≤b*S.card)
    (hH : ∀ x∈S,∀ y∈T,H x y → E x y ∨ F x y) :
    letI := Classical.propDecidable
    ((((S.product T).filter (fun p=>H p.1 p.2)).card:ℕ):ℝ) ≤
      (a+b)*S.card*T.card := by
  classical
  have hc : ((S.product T).filter (fun p=>H p.1 p.2)).card ≤
      ((S.product T).filter (fun p=>E p.1 p.2)).card+
        ((S.product T).filter (fun p=>F p.1 p.2)).card := by
    apply le_trans (Finset.card_le_card (show (S.product T).filter (fun p=>H p.1 p.2)⊆
      ((S.product T).filter (fun p=>E p.1 p.2))∪((S.product T).filter (fun p=>F p.1 p.2)) from ?_))
      (Finset.card_union_le _ _)
    intro p hp
    obtain ⟨hm,hh⟩:=Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩:=Finset.mem_product.mp hm
    rcases hH p.1 hx p.2 hy hh with he|hf
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hm,hf⟩)
  have he : (((S.product T).filter (fun p=>E p.1 p.2)).card:ℝ) ≤ S.card*(a*T.card) := by
    rw [filter_card_product_left S T E,Nat.cast_sum]
    simpa using Finset.sum_le_sum hE
  have hf : (((S.product T).filter (fun p=>F p.1 p.2)).card:ℝ) ≤ T.card*(b*S.card) := by
    rw [filter_card_product_right S T F,Nat.cast_sum]
    simpa using Finset.sum_le_sum hF
  have hc' : (((S.product T).filter (fun p=>H p.1 p.2)).card:ℝ) ≤
      (((S.product T).filter (fun p=>E p.1 p.2)).card:ℝ)+
        (((S.product T).filter (fun p=>F p.1 p.2)).card:ℝ) := by exact_mod_cast hc
  nlinarith

lemma time_positive_rough {S : ℝ} {r L : ℤ} {w : ℕ} (hS : 0<S) (hL : 0<L)
    (hr : r.natAbs.Coprime (primorial w)) (hWL : (primorial w:ℤ)∣L)
    {t : ℤ} (ht : t∈times S r L) : 0<t ∧ Rough w t ∧ (t:ℝ)<2*S := by
  obtain ⟨hs,hi,z,rfl⟩ := (mem_times _ _ _ _ hL).mp ht
  refine ⟨by exact_mod_cast hS.trans_le hs,?_,hi⟩
  exact RoughProgressionDensity.rough_add_multiple ((rough_iff_coprime _ _).mpr hr) hWL z

lemma productTimes_nonempty_eventually {m : ℕ} (S : ℕ → Fin m → ℝ)
    (r : ℕ → Fin m → ℤ) (L : ℕ → ℤ) (hL : ∀ n,0<L n)
    (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ᶠ n in atTop,(productTimes (S n) (r n) (L n)).Nonempty := by
  classical
  have hh : ∀ j,∀ᶠ n in atTop,0<(times (S n j) (r n j) (L n)).card := by
    intro j
    have hlen:=timeLength_tendsto (r:=fun n=>r n j) hL (hS j) (hSL j)
    filter_upwards [hlen.eventually (eventually_gt_atTop 0)] with n hn
    rw [times_card _ _ _ (hL n)]
    exact_mod_cast hn
  filter_upwards [eventually_all.mpr hh] with n hn
  simp only [productTimes,Fintype.piFinset_nonempty,Finset.card_pos] at *
  exact hn

end RoughProductRemoval
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional
open scoped BigOperators

lemma residue_normalize {v : ℕ} (d : ℕ) (hd : 0<d) (a : Fin v → ℤ) :
    ∃ R : Fin v → Fin d,∀ i,a i ≡ ((R i).val:ℤ) [ZMOD d] := by
  have h (i : Fin v) : ∃ k : Fin d,a i ≡ (k.val:ℤ) [ZMOD d] := by
    have hd' : (0:ℤ)<d := by exact_mod_cast hd
    let k : Fin d := ⟨(a i % d).toNat, by
      have hb := Int.emod_lt_of_pos (a i) hd'
      have hb0 := Int.emod_nonneg (a i) hd'.ne'
      omega⟩
    refine ⟨k,?_⟩
    have hk : (k.val:ℤ)=a i%d := Int.toNat_of_nonneg (Int.emod_nonneg _ hd'.ne')
    rw [hk]
    simp [Int.ModEq]
  exact Classical.skolem.mp h

lemma physicalResidueBox_congr {v : ℕ} (lo hi : Fin v → ℝ) (a b : Fin v → ℤ)
    (d : ℕ) (h : ∀ i,a i ≡ b i [ZMOD d]) :
    physicalResidueBox lo hi a d=physicalResidueBox lo hi b d := by
  classical
  unfold physicalResidueBox
  congr 1
  funext x
  apply propext
  exact forall_congr' (fun i=>⟨fun hx=>hx.trans (h i),fun hx=>hx.trans (h i).symm⟩)

lemma nestedBox_congr {v : ℕ} (lo hi : Fin v → ℝ) (a b A : Fin v → ℤ)
    (d M : ℕ) (q : ℤ) (h : ∀ i,a i ≡ b i [ZMOD d]) :
    nestedBox lo hi a A d M q=nestedBox lo hi b A d M q := by
  unfold nestedBox
  rw [physicalResidueBox_congr lo hi a b d h]

variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]

def firstBad (m v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (d M : ℕ) (A : Fin v → ℤ) (P : (Fin ((m+1)+v) → ℝ) → G)
    (s : ℤ) (t : Fin m → ℤ) : Prop :=
  ∃ (lo hi : Fin v → ℝ) (res : Fin v → ℤ) (test : (G⧸Γ) → ℂ),
    (∀ i,c₀*Z≤hi i-lo i) ∧ (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (nestedBox lo hi res A d M (∏ j,t j))
      (fun x=>test (QuotientGroup.mk (P (Fin.append (fun j=>((consPair (s,t) j):ℝ)) (fun i=>(x i:ℝ))))))-
    mean (nestedBox lo hi res A d M ((∏ j,t j)*s))
      (fun x=>test (QuotientGroup.mk (P (Fin.append (fun j=>((consPair (s,t) j):ℝ)) (fun i=>(x i:ℝ))))))‖

omit [TopologicalSpace G] in
lemma badProduct_succ_split {m v : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z : ℝ}
    {d M : ℕ} {A : Fin v → ℤ} {P : (Fin ((m+1)+v) → ℝ) → G}
    {s : ℤ} {t : Fin m → ℤ}
    (h : badProduct Γ (m+1) v c₀ C₀ B η Z d M A P (consPair (s,t))) :
    badProduct Γ m v c₀ C₀ B (η/2) Z d M A (fun y=>P (tailLift (s:ℝ) y)) t ∨
      firstBad Γ m v c₀ C₀ B (η/2) Z d M A P s t := by
  obtain ⟨lo,hi,res,test,hside,hbox,hlip,hbound,hdisc⟩ := h
  let f (x : Fin v → ℤ) := test (QuotientGroup.mk
    (P (Fin.append (fun j=>((consPair (s,t) j):ℝ)) (fun i=>(x i:ℝ)))) )
  have hf : (fun x : Fin v → ℤ=>test (QuotientGroup.mk
      (P (tailLift (s:ℝ) (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))))=f := by
    funext x
    simp only [tailLift_eval,f,consPair]
    congr 4
    funext j
    exact Fin.cases (by simp) (fun k=>by simp) j
  have hp : (∏ j,consPair (s,t) j)=(∏ j,t j)*s := by
    simp only [Fin.prod_univ_succ,consPair,Fin.cons_zero,Fin.cons_succ,mul_comm]
  rw [hp] at hdisc
  have htri := norm_sub_le_norm_sub_add_norm_sub (mean (physicalResidueBox lo hi res d) f)
    (mean (nestedBox lo hi res A d M (∏ j,t j)) f)
    (mean (nestedBox lo hi res A d M ((∏ j,t j)*s)) f)
  by_cases h₁ : η/2≤‖mean (physicalResidueBox lo hi res d) f-
      mean (nestedBox lo hi res A d M (∏ j,t j)) f‖
  · left
    refine ⟨lo,hi,res,test,hside,hbox,hlip,hbound,?_⟩
    simpa only [hf] using h₁
  · right
    exact ⟨lo,hi,res,test,hside,hbox,hlip,hbound,by dsimp [f] at *; linarith⟩

variable (c : RealCoordinates G dim)

 
theorem firstBad_reduction {m v D : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z : ℝ}
    (d M : ℕ) (hd : 0<d) (hC : 0≤C₀) (A : Fin v → ℤ)
    (P : (Fin ((m+1)+v)→ℝ)→G)
    (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (t : Fin m → ℤ) (ht : ∀ j,0<t j)
    (hdq : d.Coprime (∏ j,(t j).natAbs)) (hMq : M.Coprime (∏ j,(t j).natAbs))
    (hZ : ((d*(∏ j,(t j).natAbs):ℕ):ℝ)≤Z) :
    ∃ Q : (Fin v → Fin d) → (Fin (v+1)→ℝ)→G,
      (∀ R i,HasDegree (fun y=>canonicalLog c (Q R y) i) D) ∧
      ∀ s : ℤ,0<s →(M*d).Coprime s.natAbs →
        firstBad Γ m v c₀ C₀ B η Z d M A P s t →
        ∃ R,RoughProgressionDensity.BadAt Γ v c₀ (C₀+1) B η
          (Z/(d*(∏ j,(t j).natAbs):ℕ)) (Q R) s := by
  classical
  let q : ℕ := ∏ j,(t j).natAbs
  have hq : 0<q := Finset.prod_pos (fun j _=>Int.natAbs_pos.mpr (ht j).ne')
  have hqe : (q:ℤ)=∏ j,t j := by
    dsimp [q]
    rw [Nat.cast_prod]
    congr 1
    funext j
    exact (Int.natCast_natAbs _).trans (abs_of_pos (ht j))
  have hh (R : Fin v → Fin d) := nested_residue_means d M q hd hq hdq hMq
    (fun i=>(R i).val) A
  choose u hu hem using hh
  refine ⟨fun R y=>P (firstLift (fun j=>(t j:ℝ)) (u R) (d*q) y),
    fun R=>first_polynomial c P hP _ _ _,?_⟩
  intro s hs hMs hbad
  obtain ⟨lo,hi,res,test,hside,hbox,hlip,hbound,hdisc⟩ := hbad
  obtain ⟨R,hR⟩ := residue_normalize d hd res
  obtain ⟨b,hb⟩ := hem R s.natAbs hMs
  have htcast : (s.natAbs:ℤ)=s := (Int.natCast_natAbs _).trans (abs_of_pos hs)
  have heq : ((q*s.natAbs:ℕ):ℤ)=(∏ j,t j)*s := by rw [Nat.cast_mul,hqe,htcast]
  let f (x : Fin v → ℤ) := test (QuotientGroup.mk
    (P (Fin.append (fun j=>((consPair (s,t) j):ℝ)) (fun i=>(x i:ℝ)))) )
  have hh := hb lo hi f
  rw [hqe] at hh
  rw [htcast] at hh
  rw [nestedBox_congr lo hi res (fun i=>(R i).val) A d M (∏ j,t j) hR,
    nestedBox_congr lo hi res (fun i=>(R i).val) A d M ((∏ j,t j)*s) hR] at hdisc
  change η≤‖mean _ f-mean _ f‖ at hdisc
  rw [hh.1,hh.2] at hdisc
  have hgeom := rescaled_geometry lo hi (u R) (d*q) (Nat.mul_pos hd hq)
    Z C₀ c₀ hZ hC (fun i=>⟨(hu R i).1,(hu R i).2.le⟩) (by simpa only [neg_mul] using hbox) hside
  refine ⟨R,rescaledEndpoint lo (u R) (d*q),rescaledEndpoint hi (u R) (d*q),
    b,test,(fun i=>(hgeom i).2.2),(fun i=>⟨(hgeom i).1,(hgeom i).2.1⟩),hlip,hbound,?_⟩
  simpa only [firstLift_eval,consPair,f] using hdisc

end RoughProductRemoval

end
end

end OAI
