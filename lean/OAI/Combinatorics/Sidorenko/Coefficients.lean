import OAI.Combinatorics.Sidorenko.Activation

namespace OAI


section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def labelProduct (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K) : ℝ :=
  ∏ k,A k (α (cornerPairL k)) (α (cornerPairR k))
noncomputable def nonemptyLabels : Finset (Fin 33 → Finset K) := Finset.univ.filter (fun α => ∀ e,α e≠∅)
lemma mem_nonemptyLabels (α : Fin 33 → Finset K) : α∈nonemptyLabels ↔ ∀ e,α e≠∅ := by
  simp only [nonemptyLabels,Finset.mem_filter,Finset.mem_univ,true_and]
noncomputable def activeCoefficient (A : ActCorner → Finset K → Finset K → ℝ) : ℝ :=
  ∑ α∈nonemptyLabels,labelProduct A α

omit [Fintype K] [DecidableEq K] in
lemma labelProduct_nonzero (A : ActCorner → Finset K → Finset K → ℝ) (α : Fin 33 → Finset K)
    (h : labelProduct A α≠0) (k : ActCorner) : A k (α (cornerPairL k)) (α (cornerPairR k))≠0 :=
  (Finset.prod_ne_zero_iff.mp h) k (Finset.mem_univ k)

lemma empty_propagation (P : Fin 33 → Prop) (hs : ∀ j p q,P (facePair j p) ↔ P (facePair j q)) :
    ∀ e,P e ↔ P 0 := by
  have hstep (e : Fin 33) : P e ↔ P (pairParent e) := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    simpa only [hi,hk] using hs (pairBridge e) i k
  have hmain : ∀ m,∀ e : Fin 33,e.val=m → (P e ↔ P 0) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem
      by_cases he : e=0
      · subst e; rfl
      · exact (hstep e).trans (ih _ (by simpa only [hem] using pairParent_lt e he) _ rfl)
  intro e; exact hmain e.val e rfl

lemma labelProduct_empty_dichotomy (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) (α : Fin 33 → Finset K)
    (h : labelProduct (fun k => activationMoment (p k)) α≠0) :
    (∀ e,α e=∅) ∨ (∀ e,α e≠∅) := by
  have hs (k : ActCorner) : α (cornerPairL k)=∅ ↔ α (cornerPairR k)=∅ := by
    have hn := labelProduct_nonzero _ _ h k
    constructor
    · intro he
      by_contra hr
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,one_mul] at hn
      exact hn (hp k _ hr)
    · intro he
      by_contra hl
      rw [he,activationMoment] at hn
      simp only [activationPhi_empty,mul_one] at hn
      exact hn (hp k _ hl)
  have hf (j : Fin 22) (a b : Fin 3) : α (facePair j a)=∅ ↔ α (facePair j b)=∅ := by
    have h0 := hs (j,0); have h1 := hs (j,1); have h2 := hs (j,2)
    change (α (facePair j 0)=∅ ↔ α (facePair j 1)=∅) at h0
    change (α (facePair j 0)=∅ ↔ α (facePair j 2)=∅) at h1
    change (α (facePair j 1)=∅ ↔ α (facePair j 2)=∅) at h2
    fin_cases a <;> fin_cases b <;> tauto
  have ht := empty_propagation (fun e => α e=∅) hf
  by_cases hz : α 0=∅
  · exact Or.inl (fun e => (ht e).mpr hz)
  · exact Or.inr (fun e he => hz ((ht e).mp he))

lemma allCoefficient_eq (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α)=
      1+activeCoefficient (fun k => activationMoment (p k)) := by
  classical
  let z : Fin 33 → Finset K := fun _ => ∅
  have hz : z∉(nonemptyLabels : Finset (Fin 33 → Finset K)) := by simp [nonemptyLabels,z]
  have hi : (insert z nonemptyLabels : Finset (Fin 33 → Finset K))⊆Finset.univ := Finset.subset_univ _
  have he := Finset.sum_subset hi (f := labelProduct (fun k => activationMoment (p k)))
  rw [←he,Finset.sum_insert hz]
  · simp [labelProduct,z,activeCoefficient]
  · intro α _ hα
    by_contra hn
    rcases labelProduct_empty_dichotomy p hp α hn with h|h
    · have : α=z := funext h
      exact hα (by simp [this])
    · exact hα (Finset.mem_insert_of_mem (by simpa [nonemptyLabels] using h))
lemma activeCoefficient_unique (A : ActCorner → Finset K → Finset K → ℝ)
    (α₀ : Fin 33 → Finset K) (h₀ : ∀ e,α₀ e≠∅)
    (hu : ∀ α,(∀ e,α e≠∅) → labelProduct A α≠0 → α=α₀) :
    activeCoefficient A=labelProduct A α₀ := by
  unfold activeCoefficient
  apply Finset.sum_eq_single α₀
  · intro α hα hne
    by_contra hn
    exact hne (hu α ((mem_nonemptyLabels α).mp hα) hn)
  · intro hn; exact (hn ((mem_nonemptyLabels α₀).mpr h₀)).elim

end Coefficients

lemma identity_labels_forced (α : Fin 33 → Finset ActCorner) (hne : ∀ e,α e≠∅)
    (h : labelProduct (fun k => activationMoment (cornerLaw k)) α≠0) : α=pairCorners := by
  have hl (k : ActCorner) := labelProduct_nonzero _ _ h k
  have hsub (e : Fin 33) : α e⊆pairCorners e := by
    intro k hk
    apply (corner_support e k).mp
    intro b hb
    have hs := cornerLaw_support b _ _ (hl b)
    rcases (pairCorners_mem b e).mp hb with hb|hb
    · exact hs (Finset.mem_union_left _ (by simpa only [hb] using hk))
    · exact hs (Finset.mem_union_right _ (by simpa only [hb] using hk))
  have hmem (k : ActCorner) : k∈α (cornerPairL k) ∧ k∈α (cornerPairR k) := by
    have hd : ¬Disjoint (α (cornerPairL k)) (α (cornerPairR k)) := by
      intro hd
      apply hl k
      exact cornerLaw_disjoint k _ _ hd (fun he => hne _ ((Finset.union_eq_empty.mp he).1))
    obtain ⟨b,hbl,hbr⟩ := Finset.not_disjoint_iff.mp hd
    have hb : b∈pairCorners (cornerPairL k) ∩ pairCorners (cornerPairR k) :=
      Finset.mem_inter.mpr ⟨hsub _ hbl,hsub _ hbr⟩
    rw [pairCorners_inter,Finset.mem_singleton] at hb
    simpa only [hb] using And.intro hbl hbr
  funext e
  apply Finset.Subset.antisymm (hsub e)
  intro k hk
  rcases (pairCorners_mem k e).mp hk with hk|hk
  · simpa only [hk] using (hmem k).1
  · simpa only [hk] using (hmem k).2

lemma identity_labelProduct : labelProduct (fun k => activationMoment (cornerLaw k)) pairCorners= -(1/4:ℝ)^66 := by
  unfold labelProduct
  simp_rw [cornerLaw_value,div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  have hs : (∏ k : ActCorner,cornerSigma k)= -1 := by
    rw [Finset.prod_eq_single (0,0)]
    · simp [cornerSigma]
    · intro b _ hb; simp [cornerSigma,hb]
    · simp
  rw [hs]
  simp [Fintype.card_prod]

lemma pairCorners_nonempty (e : Fin 33) : pairCorners e≠∅ := by
  intro he
  have := pairCorners_card e
  rw [he] at this
  simp at this

lemma identity_activeCoefficient : activeCoefficient (fun k => activationMoment (cornerLaw k))= -(1/4:ℝ)^66 := by
  rw [activeCoefficient_unique _ pairCorners pairCorners_nonempty identity_labels_forced]
  exact identity_labelProduct
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
noncomputable def activationEntry (z : Activation K) (k : K) : ℝ := if k∈z.1 then boolSign (z.2 k) else 0
omit [Fintype K] in
lemma activationPhi_product (α : Finset K) (z : Activation K) :
    activationPhi α z=∏ k∈α,activationEntry z k := by
  unfold activationPhi
  by_cases h : α⊆z.1
  · simp only [h,ite_true,boolMonomial]
    apply Finset.prod_congr rfl; intro k hk
    simp only [activationEntry,h hk,ite_true]
  · rw [ite_eq_right h]
    obtain ⟨k,hk,hz⟩ := Finset.not_subset.mp h
    symm; apply Finset.prod_eq_zero hk
    simp only [activationEntry,hz,ite_false]
omit [Fintype K] in
lemma activationEntry_abs (z : Activation K) (k : K) : |activationEntry z k|≤1 := by
  unfold activationEntry; split <;> simp
lemma bool_double_mean (a b : ℝ) : uniformMean (fun η : Bool => (1+boolSign η*a)*(1+boolSign η*b))=1+a*b := by
  simp [uniformMean,Fintype.card_bool,boolSign]
  ring
omit [DecidableEq K] in
lemma product_one_add_expansion {I : Type*} [Fintype I] [DecidableEq I] (f : I → K → ℝ) :
    (∏ i,∏ k,(1+f i k))=∑ α : I → Finset K,∏ i,∏ k∈α i,f i k := by
  simp_rw [Finset.prod_one_add,Finset.powerset_univ]
  exact Fintype.prod_sum _
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
def faceSlot : Fin 33 → Fin 2 → Fin 3 := ![![0, 0], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![0, 0], ![2, 0], ![1, 0], ![2, 0], ![2, 0], ![2, 1], ![1, 1], ![2, 0], ![1, 1], ![2, 1], ![1, 1], ![2, 2], ![0, 0], ![2, 0], ![0, 0], ![2, 2], ![2, 2], ![2, 2], ![2, 2], ![2, 1], ![1, 0], ![1, 0], ![1, 1], ![0, 0], ![2, 1], ![2, 0], ![1, 1], ![0, 0]]
def faceSide : Fin 22 → Fin 3 → Fin 2 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![1, 0, 0], ![1, 1, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 0], ![1, 0, 0], ![1, 0, 1], ![1, 1, 1], ![1, 0, 1], ![0, 1, 1], ![1, 1, 0], ![1, 1, 1]]
theorem faceSlot_correct : ∀ e b,facePair (pairFace e b) (faceSlot e b)=e := by decide
theorem faceSide_correct : ∀ j k,pairFace (facePair j k) (faceSide j k)=j := by decide
theorem faceSlot_side : ∀ j k,faceSlot (facePair j k) (faceSide j k)=k := by decide
theorem faceSide_slot : ∀ e b,faceSide (pairFace e b) (faceSlot e b)=b := by decide

def occurrencePairEquiv : (Fin 22 × Fin 3) ≃ (Fin 33 × Fin 2) where
  toFun a := (facePair a.1 a.2,faceSide a.1 a.2)
  invFun b := (pairFace b.1 b.2,faceSlot b.1 b.2)
  left_inv a := by simp only [faceSide_correct,faceSlot_side]
  right_inv b := by simp only [faceSlot_correct,faceSide_slot]

def pairCorner (e : Fin 33) (a : Fin 2 × Fin 2) : ActCorner :=
  (pairFace e a.1,if a.2=0 then slotLeft (faceSlot e a.1) else slotRight (faceSlot e a.1))
lemma pairCorner_image_0 : Finset.univ.image (pairCorner 0)=pairCorners 0 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_1 : Finset.univ.image (pairCorner 1)=pairCorners 1 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_2 : Finset.univ.image (pairCorner 2)=pairCorners 2 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_3 : Finset.univ.image (pairCorner 3)=pairCorners 3 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_4 : Finset.univ.image (pairCorner 4)=pairCorners 4 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_5 : Finset.univ.image (pairCorner 5)=pairCorners 5 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_6 : Finset.univ.image (pairCorner 6)=pairCorners 6 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_7 : Finset.univ.image (pairCorner 7)=pairCorners 7 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_8 : Finset.univ.image (pairCorner 8)=pairCorners 8 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_9 : Finset.univ.image (pairCorner 9)=pairCorners 9 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_10 : Finset.univ.image (pairCorner 10)=pairCorners 10 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_11 : Finset.univ.image (pairCorner 11)=pairCorners 11 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_12 : Finset.univ.image (pairCorner 12)=pairCorners 12 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_13 : Finset.univ.image (pairCorner 13)=pairCorners 13 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_14 : Finset.univ.image (pairCorner 14)=pairCorners 14 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_15 : Finset.univ.image (pairCorner 15)=pairCorners 15 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_16 : Finset.univ.image (pairCorner 16)=pairCorners 16 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_17 : Finset.univ.image (pairCorner 17)=pairCorners 17 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_18 : Finset.univ.image (pairCorner 18)=pairCorners 18 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_19 : Finset.univ.image (pairCorner 19)=pairCorners 19 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_20 : Finset.univ.image (pairCorner 20)=pairCorners 20 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_21 : Finset.univ.image (pairCorner 21)=pairCorners 21 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_22 : Finset.univ.image (pairCorner 22)=pairCorners 22 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_23 : Finset.univ.image (pairCorner 23)=pairCorners 23 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_24 : Finset.univ.image (pairCorner 24)=pairCorners 24 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_25 : Finset.univ.image (pairCorner 25)=pairCorners 25 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_26 : Finset.univ.image (pairCorner 26)=pairCorners 26 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_27 : Finset.univ.image (pairCorner 27)=pairCorners 27 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_28 : Finset.univ.image (pairCorner 28)=pairCorners 28 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_29 : Finset.univ.image (pairCorner 29)=pairCorners 29 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_30 : Finset.univ.image (pairCorner 30)=pairCorners 30 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_31 : Finset.univ.image (pairCorner 31)=pairCorners 31 := by
  rw [pairCorners_table]
  decide
lemma pairCorner_image_32 : Finset.univ.image (pairCorner 32)=pairCorners 32 := by
  rw [pairCorners_table]
  decide
theorem pairCorner_image (e : Fin 33) : Finset.univ.image (pairCorner e)=pairCorners e := by
  fin_cases e
  · exact pairCorner_image_0
  · exact pairCorner_image_1
  · exact pairCorner_image_2
  · exact pairCorner_image_3
  · exact pairCorner_image_4
  · exact pairCorner_image_5
  · exact pairCorner_image_6
  · exact pairCorner_image_7
  · exact pairCorner_image_8
  · exact pairCorner_image_9
  · exact pairCorner_image_10
  · exact pairCorner_image_11
  · exact pairCorner_image_12
  · exact pairCorner_image_13
  · exact pairCorner_image_14
  · exact pairCorner_image_15
  · exact pairCorner_image_16
  · exact pairCorner_image_17
  · exact pairCorner_image_18
  · exact pairCorner_image_19
  · exact pairCorner_image_20
  · exact pairCorner_image_21
  · exact pairCorner_image_22
  · exact pairCorner_image_23
  · exact pairCorner_image_24
  · exact pairCorner_image_25
  · exact pairCorner_image_26
  · exact pairCorner_image_27
  · exact pairCorner_image_28
  · exact pairCorner_image_29
  · exact pairCorner_image_30
  · exact pairCorner_image_31
  · exact pairCorner_image_32
theorem pairCorner_inj (e : Fin 33) : Function.Injective (pairCorner e) := by
  intro a b h
  have h1 := pairFace_injective e (congrArg Prod.fst h)
  rcases a with ⟨a,c⟩; rcases b with ⟨b,d⟩
  dsimp at h1; subst b
  have h2 := congrArg Prod.snd h
  have hn : slotLeft (faceSlot e a)≠slotRight (faceSlot e a) := by
    have hn : ∀ k : Fin 3,slotLeft k≠slotRight k := by decide
    exact hn _
  have : c=d := by fin_cases c <;> fin_cases d <;> simp_all [pairCorner]
  subst d; rfl

theorem pairCorners_product (e : Fin 33) (f : ActCorner → ℝ) :
    (∏ k∈pairCorners e,f k)=∏ b : Fin 2,
      f (pairFace e b,slotLeft (faceSlot e b))*f (pairFace e b,slotRight (faceSlot e b)) := by
  rw [←pairCorner_image,Finset.prod_image (fun _ _ _ _ h => pairCorner_inj e h),Fintype.prod_prod_type]
  apply Finset.prod_congr rfl; intro b _
  simp [Fin.prod_univ_two,pairCorner]
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type*} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
lemma FiniteLaw.mean_expansion_product (p : I → FiniteLaw A) (f : L → I → A → ℝ)
    (g : (I → A) → ℝ) (c : L → ℝ) (hg : ∀ z,g z=∑ l,∏ i,f l i (z i))
    (hc : ∀ l,(∏ i,(p i).mean (f l i))=c l) :
    (FiniteLaw.independent p).mean g=∑ l,c l := by
  calc
    _ = (FiniteLaw.independent p).mean (fun z => ∑ l,∏ i,f l i (z i)) := FiniteLaw.mean_congr _ hg
    _ = ∑ l,(FiniteLaw.independent p).mean (fun z => ∏ i,f l i (z i)) := FiniteLaw.mean_sum _ _
    _ = _ := Finset.sum_congr rfl (fun l _ => (FiniteLaw.independent_mean_product p (f l)).trans (hc l))
lemma uniformMean_double_product (a b : I → ℝ) :
    uniformMean (fun η : I → Bool => ∏ i,(1+boolSign (η i)*a i)*(1+boolSign (η i)*b i))=
    ∏ i,(1+a i*b i) := by
  rw [uniformMean_pi_product (fun i η => (1+boolSign η*a i)*(1+boolSign η*b i))]
  simp_rw [bool_double_mean]
end
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
lemma activationMoment_product (p : ActCorner → FiniteLaw (Activation K)) (α : Fin 33 → Finset K) :
    (∏ k,(p k).mean (fun z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z))=
    labelProduct (fun k => activationMoment (p k)) α := by rfl
lemma mean_activation_expansion (p : ActCorner → FiniteLaw (Activation K)) (g : (ActCorner → Activation K) → ℝ)
    (hg : ∀z,g z=∑ α : Fin 33 → Finset K,∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k)) :
    (FiniteLaw.independent p).mean g=∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
  exact FiniteLaw.mean_expansion_product (I := ActCorner) (L := Fin 33 → Finset K) (A := Activation K) p
    (fun α k z => activationPhi (α (cornerPairL k)) z*activationPhi (α (cornerPairR k)) z)
    g (labelProduct (fun k => activationMoment (p k))) hg (activationMoment_product p)
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type*} [Fintype K] [DecidableEq K]

omit [Fintype K] in
lemma labels_incidence_product (α : Fin 33 → Finset K) (z : ActCorner → Activation K) :
    (∏ e,∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
    ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  have he (e : Fin 33) : (∏ κ∈α e,∏ k∈pairCorners e,activationEntry (z k) κ)=
      ∏ k∈pairCorners e,activationPhi (α e) (z k) := by
    rw [Finset.prod_comm]; simp_rw [activationPhi_product]
  simp_rw [he,pairCorners,Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl; intro k _
  have hi (e : Fin 33) : (cornerPairL k=e ∨ cornerPairR k=e) ↔ e∈({cornerPairL k,cornerPairR k} : Finset (Fin 33)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  simp_rw [hi]
  rw [Finset.prod_ite_mem,Finset.univ_inter,Finset.prod_pair (cornerPair_ne k)]

noncomputable def expandedModel (z : ActCorner → Activation K) : ℝ :=
  ∏ κ,∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ)

lemma expandedModel_expansion (z : ActCorner → Activation K) :
    expandedModel z=∑ α : Fin 33 → Finset K,
      ∏ k,activationPhi (α (cornerPairL k)) (z k)*activationPhi (α (cornerPairR k)) (z k) := by
  unfold expandedModel
  rw [Finset.prod_comm,product_one_add_expansion]
  apply Finset.sum_congr rfl; intro α _
  exact labels_incidence_product α z

lemma expandedModel_mean (p : ActCorner → FiniteLaw (Activation K))
    (hp : ∀ k α,α≠∅ → (p k).mean (activationPhi α)=0) :
    (FiniteLaw.independent p).mean expandedModel=1+activeCoefficient (fun k => activationMoment (p k)) := by
  have he : (FiniteLaw.independent p).mean expandedModel=
      ∑ α : Fin 33 → Finset K,labelProduct (fun k => activationMoment (p k)) α := by
    apply mean_activation_expansion p expandedModel
    intro z
    exact expandedModel_expansion z
  rw [he,allCoefficient_eq p hp]

noncomputable def coordinateActive (z : ActCorner → Activation K) (κ : K) (j : Fin 22) : Finset (Fin 3) :=
  Finset.univ.filter (fun k => κ∈(z (j,k)).1)
def coordinateSigns (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) : ℤ :=
  if (z (j,k)).2 κ then 1 else -1
omit [Fintype K] [DecidableEq K] in
lemma coordinateSigns_good (z : ActCorner → Activation K) (κ : K) :
    ∀ j k,coordinateSigns z κ j k=1 ∨ coordinateSigns z κ j k= -1 := by
  intro j k; unfold coordinateSigns; split <;> tauto
omit [Fintype K] [DecidableEq K] in
lemma coordinateSigns_real (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) :
    (coordinateSigns z κ j k : ℝ)=boolSign ((z (j,k)).2 κ) := by
  unfold coordinateSigns boolSign; split <;> simp

omit [Fintype K] in
lemma coordinate_factor (z : ActCorner → Activation K) (κ : K) (j : Fin 22) (k : Fin 3) (η : Fin 33 → Bool) :
    (if slotLeft k∈coordinateActive z κ j ∧ slotRight k∈coordinateActive z κ j then
      1+(1:ℝ)*boolSign (η (facePair j k))*(coordinateSigns z κ j (slotLeft k):ℝ)*
        (coordinateSigns z κ j (slotRight k):ℝ) else 1)=
      1+boolSign (η (facePair j k))*(activationEntry (z (j,slotLeft k)) κ*activationEntry (z (j,slotRight k)) κ) := by
  simp only [coordinateActive,Finset.mem_filter,Finset.mem_univ,true_and,coordinateSigns_real,one_mul,activationEntry]
  by_cases hl : κ∈(z (j,slotLeft k)).1 <;> by_cases hr : κ∈(z (j,slotRight k)).1 <;>
    simp [hl,hr,mul_assoc]

omit [Fintype K] in
lemma coordinate_boolean_product (z : ActCorner → Activation K) (κ : K) (η : Fin 33 → Bool) :
    boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ) η=
      ∏ e,∏ b : Fin 2,(1+boolSign (η e)*
        (activationEntry (z (pairFace e b,slotLeft (faceSlot e b))) κ*
         activationEntry (z (pairFace e b,slotRight (faceSlot e b))) κ)) := by
  unfold boolConfiguration boolFacePolynomial
  simp_rw [coordinate_factor]
  let f (a : Fin 22 × Fin 3) := 1+boolSign (η (facePair a.1 a.2))*
    (activationEntry (z (a.1,slotLeft a.2)) κ*activationEntry (z (a.1,slotRight a.2)) κ)
  let g (a : Fin 33 × Fin 2) := 1+boolSign (η a.1)*
    (activationEntry (z (pairFace a.1 a.2,slotLeft (faceSlot a.1 a.2))) κ*
     activationEntry (z (pairFace a.1 a.2,slotRight (faceSlot a.1 a.2))) κ)
  change (∏ j,∏ k,f (j,k))=∏ e,∏ b,g (e,b)
  rw [←Fintype.prod_prod_type f,←Fintype.prod_prod_type g]
  exact Fintype.prod_equiv occurrencePairEquiv f g (fun a => by
    change f a=g (facePair a.1 a.2,faceSide a.1 a.2)
    simp only [f,g,faceSide_correct,faceSlot_side])

omit [Fintype K] in
lemma coordinateModel_eq (z : ActCorner → Activation K) (κ : K) :
    uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ))=
      ∏ e,(1+∏ k∈pairCorners e,activationEntry (z k) κ) := by
  let a (e : Fin 33) := activationEntry (z (pairFace e 0,slotLeft (faceSlot e 0))) κ*
    activationEntry (z (pairFace e 0,slotRight (faceSlot e 0))) κ
  let b (e : Fin 33) := activationEntry (z (pairFace e 1,slotLeft (faceSlot e 1))) κ*
    activationEntry (z (pairFace e 1,slotRight (faceSlot e 1))) κ
  calc
    _ = uniformMean (fun η : Fin 33 → Bool => ∏ e,(1+boolSign (η e)*a e)*(1+boolSign (η e)*b e)) := by
      apply uniformMean_congr; intro η
      rw [coordinate_boolean_product]
      simp only [Fin.prod_univ_two,a,b]
    _ = ∏ e,(1+a e*b e) := uniformMean_double_product a b
    _ = _ := by
      apply Finset.prod_congr rfl; intro e _
      rw [pairCorners_product]
      simp only [Fin.prod_univ_two,a,b]

lemma coordinateModels_product (z : ActCorner → Activation K) :
    (∏ κ,uniformMean (boolConfiguration 1 (coordinateActive z κ) (coordinateSigns z κ)))=expandedModel z := by
  simp_rw [coordinateModel_eq]; rfl
end Expansion
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]

noncomputable def coordinateArrayEquiv : ((I → K → A) × (J → K → B)) ≃ (K → (I → A) × (J → B)) where
  toFun x k := (fun i => x.1 i k,fun j => x.2 j k)
  invFun x := (fun i k => (x k).1 i,fun j k => (x k).2 j)
  left_inv _x := rfl
  right_inv _x := rfl

lemma uniformMean_coordinate_factor (f : K → (I → A) → (J → B) → ℝ) :
    uniformMean (fun x : (I → K → A) × (J → K → B) =>
      ∏ k,f k (fun i => x.1 i k) (fun j => x.2 j k))=
      ∏ k,uniformMean (fun x : (I → A) × (J → B) => f k x.1 x.2) := by
  have h := uniformMean_equiv (coordinateArrayEquiv (I := I) (J := J) (K := K) (A := A) (B := B))
    (fun x => ∏ k,f k (x k).1 (x k).2)
  exact h.trans (uniformMean_pi_product (fun k (x : (I → A) × (J → B)) => f k x.1 x.2))

lemma uniformMean_law_swap (p : FiniteLaw A) (f : A → B → ℝ) :
    uniformMean (fun b => p.mean (fun a => f a b))=p.mean (fun a => uniformMean (f a)) := by
  unfold uniformMean FiniteLaw.mean
  rw [Finset.sum_comm,Finset.sum_div]
  simp_rw [←Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

lemma independent_mean_equiv {C : Type*} [Fintype C]
    (e : I ≃ J) (p : J → FiniteLaw C) (f : (J → C) → ℝ) :
    (FiniteLaw.independent (fun i => p (e i))).mean (fun x => f (fun j => x (e.symm j)))=
      (FiniteLaw.independent p).mean f := by
  unfold FiniteLaw.mean FiniteLaw.independent
  let E : (I → C) ≃ (J → C) := Equiv.arrowCongr e (Equiv.refl C)
  apply Fintype.sum_equiv E
  intro x
  dsimp [E]
  congr 1
  symm
  exact Fintype.prod_equiv e.symm _ _ (fun j => by simp)

lemma independent_mean_prod (p : I → FiniteLaw A) (q : I → FiniteLaw B) (f : (I → A × B) → ℝ) :
    (FiniteLaw.independent (fun i => (p i).prod (q i))).mean f=
      (FiniteLaw.independent p).mean (fun x => (FiniteLaw.independent q).mean (fun y => f (fun i => (x i,y i)))) := by
  unfold FiniteLaw.mean FiniteLaw.independent FiniteLaw.prod
  simp_rw [Finset.mul_sum,←mul_assoc,←Finset.prod_mul_distrib]
  rw [←Fintype.sum_prod_type (fun xy : (I → A) × (I → B) =>
    (∏ i,(p i).weight (xy.1 i)*(q i).weight (xy.2 i))*f (fun i => (xy.1 i,xy.2 i)))]
  let e : (I → A × B) ≃ ((I → A) × (I → B)) := {
    toFun x := (fun i => (x i).1,fun i => (x i).2)
    invFun x i := (x.1 i,x.2 i)
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => by rfl)
end Fubini
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators

theorem faceVertex_mem (j : Fin 22) (k : Fin 3) : faceVertex j k∈faces j := by
  rw [faceVertex_correct]
  fin_cases k <;> simp

theorem faceVertex_surj (j : Fin 22) (i : Fin 13) (hi : i∈faces j) : ∃ k,faceVertex j k=i := by
  rw [faceVertex_correct] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with h|h|h
  · exact ⟨0,h.symm⟩
  · exact ⟨1,h.symm⟩
  · exact ⟨2,h.symm⟩

theorem corners_product {M : Type*} [CommMonoid M] (B : Finset (Fin 13 × Fin 22))
    (hB : B⊆corners) (f : Fin 13 × Fin 22 → M) :
    (∏ c∈B,f c)=∏ j,∏ k∈faceActive B j,f (faceVertex j k,j) := by
  rw [Finset.prod_sigma' Finset.univ (faceActive B) (fun j k => f (faceVertex j k,j))]
  symm
  apply Finset.prod_bij (fun a _ => (faceVertex a.1 a.2,a.1))
  · intro a ha
    have h := (Finset.mem_sigma.mp ha).2
    exact (Finset.mem_filter.mp h).2
  · intro a ha b hb he
    have h1 : a.1=b.1 := congrArg Prod.snd he
    rcases a with ⟨j,k⟩; rcases b with ⟨l,m⟩
    dsimp at h1; subst l
    have h2 := faceVertex_injective j (congrArg Prod.fst he)
    change k=m at h2
    subst m; rfl
  · intro b hb
    have hi : b.1∈faces b.2 := (Finset.mem_filter.mp (hB hb)).2
    obtain ⟨k,hk⟩ := faceVertex_surj b.2 b.1 hi
    refine ⟨⟨b.2,k⟩,?_,?_⟩
    · simp only [Finset.mem_sigma,Finset.mem_univ,true_and,faceActive,Finset.mem_filter]
      simpa only [hk,true_and,Prod.eta] using hb
    · simp only [hk,Prod.eta]
  · intros; rfl

theorem faceSigns_good (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ)
    (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1) : ∀ j k,faceSigns B ξ j k=1 ∨ faceSigns B ξ j k= -1 := by
  intro j k
  unfold faceSigns
  split_ifs with h
  · exact hξ _ h
  · exact Or.inl rfl

theorem layerCorrelation_configuration (r : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ) :
    layerCorrelation (2*r) q B ξ=uniformMean (configurationProduct (K := ZMod q.val) r (faceActive B) (faceSigns B ξ)) := by
  have hm : 2*r/2=r := by omega
  unfold layerCorrelation
  rw [uniformMean_prod]
  apply uniformMean_congr; intro X
  have he (Y : Fin 22 → SymMatrix (ZMod q.val) (2*r)) :
      (∏ c∈B, rankKernel (ZMod q.val) (2*r) (2*r/2) (ξ c) (X c.1-Y c.2))=
      ∏ j,∏ k∈faceActive B j,rankKernel (ZMod q.val) (2*r) r (faceSigns B ξ j k) (X (faceVertex j k)-Y j) := by
    rw [corners_product B hB]
    apply Finset.prod_congr rfl; intro j _
    apply Finset.prod_congr rfl; intro k hk
    have hk := (Finset.mem_filter.mp hk).2
    simp only [faceSigns,hk,ite_true,hm]
  simp_rw [he]
  exact uniformMean_pi_product (fun j y => ∏ k ∈ faceActive B j,
    rankKernel (ZMod q.val) (2*r) r (faceSigns B ξ j k) (X (faceVertex j k)-y))

theorem pair_sub_face_iff : ∀ (j : Fin 22) (e : Fin 33),
    pairVertices e⊆faces j ↔ ∃ k,facePair j k=e := by decide

theorem product_facePair (j : Fin 22) (f : Fin 33 → ℝ)
    (hf : ∀ e,¬pairVertices e⊆faces j → f e=1) : (∏ e,f e)=∏ k,f (facePair j k) := by
  let S := Finset.univ.image (facePair j)
  have he : (∏ e,f e)=∏ e∈S,f e := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    apply hf e
    rw [pair_sub_face_iff]
    simpa only [S,Finset.mem_image,Finset.mem_univ,true_and] using he
  rw [he]
  exact Finset.prod_image (fun _ _ _ _ h => facePair_injective j h)

theorem modelFace_polynomial (c : ℝ) (B : Finset (Fin 13 × Fin 22))
    (ξ : Fin 13 × Fin 22 → ℤ) (η : Fin 33 → Bool) (j : Fin 22) :
    (∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
      1+c*boolSign (η (pairModelEquiv.symm e))*∏ i∈e.val,(ξ (i,j):ℝ) else 1)=
    boolFacePolynomial c (faceActive B j) (faceSigns B ξ j) j η := by
  rw [←Equiv.prod_comp pairModelEquiv]
  simp only [Equiv.symm_apply_apply]
  change (∏ e : Fin 33,if pairVertices e⊆faces j ∧ (∀ i∈pairVertices e,(i,j)∈B) then
      1+c*boolSign (η e)*∏ i∈pairVertices e,(ξ (i,j):ℝ) else 1)=_
  rw [product_facePair j _ (fun e he => ite_eq_right (by tauto))]
  apply Finset.prod_congr rfl; intro k _
  have hf : pairVertices (facePair j k)⊆faces j := (pair_sub_face_iff j _).mpr ⟨k,rfl⟩
  have hp : pairVertices (facePair j k)={faceVertex j (slotLeft k),faceVertex j (slotRight k)} := by
    rw [pair_endpoints,(facePair_endpoints j k).1,(facePair_endpoints j k).2]
  have hne : faceVertex j (slotLeft k)≠faceVertex j (slotRight k) := by
    rw [←(facePair_endpoints j k).1,←(facePair_endpoints j k).2]
    exact pair_endpoints_ne _
  simp only [hf,true_and]
  simp only [hp,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq,
    Finset.prod_pair hne,faceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases h : (faceVertex j (slotLeft k),j)∈B ∧ (faceVertex j (slotRight k),j)∈B
  · simp only [faceSigns,h.1,h.2,and_self,ite_true]; ring
  · simp only [h,ite_false]

noncomputable def pairBoolEquiv : (Fin 33 → Bool) ≃ (ModelPair → Bool) where
  toFun η := η ∘ pairModelEquiv.symm
  invFun η := η ∘ pairModelEquiv
  left_inv η := by funext e; simp
  right_inv η := by funext e; simp

theorem signModelCorrelation_configuration (r : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) :
    signModelCorrelation (2*r) q B ξ=uniformMean
      (boolConfiguration (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) (faceActive B) (faceSigns B ξ)) := by
  unfold signModelCorrelation
  simp only [show 2*r/2=r by omega]
  rw [←uniformMean_equiv pairBoolEquiv]
  apply uniformMean_congr; intro η
  change (∏ j, ∏ e : ModelPair, if e.val⊆faces j ∧ (∀ i∈e.val,(i,j)∈B) then
    1+(quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r):ℝ)*boolSign (η (pairModelEquiv.symm e))*
      ∏ i∈e.val,(ξ (i,j):ℝ) else 1)=_
  apply Finset.prod_congr rfl; intro j _
  exact modelFace_polynomial _ B ξ η j
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators

noncomputable def boolTestError (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ) (q : OddPrime) : ℝ :=
  uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) => boolConfiguration c T ξ (pairBool X))-
    uniformMean (boolConfiguration c T ξ)

theorem boolTestError_tendsto (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (c : ℝ) : Tendsto
    (boolTestError r T ξ c) primeInfinity (nhds 0) := by
  unfold boolTestError
  simpa only [sub_self] using
    (pairBool_test_tendsto (2*r) (even_two_mul r) hbig (boolConfiguration c T ξ)).sub_const
      (uniformMean (boolConfiguration c T ξ))

theorem varyingBoolTestError_tendsto (r : ℕ) (hbig : 12≤2*r) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : Tendsto
    (fun q : OddPrime => boolTestError r T ξ
      (quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)) q) primeInfinity (nhds 0) := by
  have ht := ((boolTestError_tendsto r hbig T ξ 1).abs).add ((boolTestError_tendsto r hbig T ξ (-1)).abs)
  simp only [abs_zero,add_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  rcases quadraticChar_dichotomy (F := ZMod q.val) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) with h|h
  · simp only [h,Int.cast_one]; exact le_add_of_nonneg_right (abs_nonneg _)
  · simp only [h,Int.cast_neg,Int.cast_one]; exact le_add_of_nonneg_left (abs_nonneg _)

theorem rankLayerConvergence (r : ℕ) (hlarge : singularTailThreshold≤2*r)
    (B : Finset (Fin 13 × Fin 22)) (hB : B⊆corners) (ξ : Fin 13 × Fin 22 → ℤ)
    (hξ : ∀ c∈B,ξ c=1 ∨ ξ c= -1) : Tendsto
      (fun q : OddPrime => layerCorrelation (2*r) q B ξ-signModelCorrelation (2*r) q B ξ)
      primeInfinity (nhds 0) := by
  have hb : 12≤2*r := by have := singularTailThreshold_large; omega
  have h1 := configuration_bool_tendsto r (faceActive B) (faceSigns B ξ) (faceSigns_good B ξ hξ) hlarge
  have h2 := varyingBoolTestError_tendsto r hb (faceActive B) (faceSigns B ξ)
  have ht := h1.add h2
  simp only [add_zero] at ht
  convert ht using 1
  funext q
  rw [layerCorrelation_configuration r q B hB ξ,signModelCorrelation_configuration]
  unfold boolTestError
  ring

theorem rankLayerLimit_proved : RankLayerLimit := by
  refine ⟨singularTailThreshold,?_,?_⟩
  · have := singularTailThreshold_large; omega
  intro D hD he B hB ξ hξ
  obtain ⟨r,hr⟩ := he
  have h : D=2*r := by omega
  rw [h] at hD ⊢
  exact rankLayerConvergence r hD B hB ξ hξ
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Filter
instance primeInfinity_neBot : NeBot primeInfinity := by
  apply Filter.comap_neBot
  intro s hs
  obtain ⟨N,hN⟩ := Filter.mem_atTop_sets.mp hs
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨⟨q,hprime,by omega⟩,hN q (by omega)⟩
end SidorenkoCounterexample

end

end OAI
