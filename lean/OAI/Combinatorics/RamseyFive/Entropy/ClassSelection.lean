import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FiniteKernels
import OAI.Combinatorics.RamseyFive.Entropy.SubsetDeficit

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {Ω ι κ : Type*} [Fintype Ω] [Fintype κ] [Nonempty κ]

def classPositions (S : Finset ι) (c : ι → κ) (a : κ) : Finset ι := S.filter (fun i=>c i=a)

lemma exists_large_class (S : Finset ι) (c : ι → κ) (r : ℕ)
    (h : Fintype.card κ*r ≤ S.card) : ∃ a,r ≤ (classPositions S c a).card := by
  obtain ⟨a,_,ha⟩:=Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s:=S) (t:=Finset.univ) (f:=c) (fun _ _=>Finset.mem_univ _) Finset.univ_nonempty
    (by simpa using h)
  exact ⟨a,ha⟩

theorem fixed_large_class (p : Law Ω) (S : Ω → Finset ι) (c : Ω → ι → κ) (r : ℕ)
    (h : ∀ ω,0 < p ω → Fintype.card κ*r ≤ (S ω).card) :
    ∃ a,(1:ℝ)/Fintype.card κ ≤
      eventMass p (Finset.univ.filter fun ω=>r ≤ (classPositions (S ω) (c ω) a).card) := by
  let choose : Ω → κ := fun ω=>if hp : 0 < p ω then
    (exists_large_class (S ω) (c ω) r (h ω hp)).choose else Classical.choice inferInstance
  have hchoose : ∀ ω,0 < p ω → r ≤ (classPositions (S ω) (c ω) (choose ω)).card := by
    intro ω hp
    simp only [choose,dite_eq_left hp]
    exact (exists_large_class (S ω) (c ω) r (h ω hp)).choose_spec
  have hex : ∃ a,(1:ℝ)/Fintype.card κ ≤ map p choose a := by
    have hcard : (0:ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    by_contra! hh
    have hs : (∑ a,map p choose a) < ∑ _a:κ,(1:ℝ)/Fintype.card κ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _=>hh a)
    rw [(map p choose).sum_one] at hs
    have he : (∑ _a:κ,(1:ℝ)/Fintype.card κ)=1 := by simp [hcard.ne']
    rw [he] at hs
    exact lt_irrefl _ hs
  obtain ⟨a,ha⟩:=hex
  refine ⟨a,ha.trans ?_⟩
  simp only [eventMass, Finset.sum_filter]
  change (∑ ω,if choose ω=a then p ω else 0) ≤
    ∑ ω,if r ≤ (classPositions (S ω) (c ω) a).card then p ω else 0
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < p ω
  · by_cases he : choose ω=a
    · have hω : ω∈Finset.univ.filter (fun ω=>r ≤ (classPositions (S ω) (c ω) a).card) := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,he ▸ hchoose ω hp⟩
      rw [ite_eq_left he,ite_eq_left ((Finset.mem_filter.mp hω).2)]
    · rw [ite_eq_right he]
      split_ifs <;> first | exact p.nonneg ω | exact le_rfl
  · have hz : p ω=0 := le_antisymm (le_of_not_gt hp) (p.nonneg ω)
    simp only [hz,ite_self,le_refl]

variable {α β : Type*} [Fintype α] [Fintype β]

def conditionContext (p : Law (α×β)) (E : Finset α) (hE : 0 < eventMass (first p) E) :
    Law (α×β) := adaptiveLaw (conditionOn (first p) E hE) (fiber p)

lemma conditionContext_fiber (p : Law (α×β)) (E : Finset α)
    (hE : 0 < eventMass (first p) E) (a : α) (ha : 0 < conditionOn (first p) E hE a) :
    fiber (conditionContext p E hE) a=fiber p a := fiber_adaptive _ _ _ ha

lemma conditionContext_mass (p : Law (α×β)) (E : Finset α)
    (hE : 0 < eventMass (first p) E) (a : α) (b : β) :
    conditionContext p E hE (a,b)=if a∈E then p (a,b)/eventMass (first p) E else 0 := by
  change conditionOn (first p) E hE a*fiber p a b=_
  rw [conditionOn_apply]
  split_ifs
  · rw [div_mul_eq_mul_div,←mass_eq_first_mul_fiber]
  · exact zero_mul _

lemma conditionContext_pointwise (p : Law (α×β)) (E : Finset α)
    (hE : 0 < eventMass (first p) E) (z : α×β) :
    conditionContext p E hE z ≤ p z/eventMass (first p) E := by
  rw [conditionContext_mass]
  split_ifs
  · rfl
  · exact div_nonneg (p.nonneg _) hE.le

lemma conditionContext_positive (p : Law (α×β)) (E : Finset α)
    (hE : 0 < eventMass (first p) E) (z : α×β) (hz : 0 < conditionContext p E hE z) :
    z.1∈E  ∧  0 < p z := by
  rw [conditionContext_mass] at hz
  split_ifs at hz with he
  · exact ⟨he,(div_pos_iff.mp hz).resolve_right (fun h=>hE.not_gt h.2) |>.1⟩
  · exact (lt_irrefl _ hz).elim

end

open scoped Classical BigOperators
variable {I J β κ : Type*} [Fintype I] [Fintype J] [Fintype β] [Fintype κ]
local instance contextRestrictIDecEq : DecidableEq I := Classical.decEq _
local instance contextRestrictJDecEq : DecidableEq J := Classical.decEq _
local instance contextRestrictSubtypeDecEq (S : Finset I) : DecidableEq S := Classical.decEq _

def embeddingRange (f : J↪I) : Finset I := Finset.univ.image f

def embeddingRangeEquiv (f : J↪I) : J≃embeddingRange f :=
  Equiv.ofBijective (fun j=>⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun a b h=>f.injective (congrArg Subtype.val h),by
      intro z
      obtain ⟨j,_,hj⟩:=Finset.mem_image.mp z.property
      exact ⟨j,Subtype.ext hj⟩⟩

omit [Fintype I] in
lemma embeddingRange_card (f : J↪I) : (embeddingRange f).card=Fintype.card J := by
  unfold embeddingRange
  rw [Finset.card_image_of_injective _ f.injective,Finset.card_univ]

lemma entropy_reindex_range (p : Law (I→β)) (f : J↪I) :
    entropy (map p (fun x=>x ∘ f))=
      entropy (map p (fun x=>fun i : embeddingRange f=>x i.val)) := by
  let e:=embeddingRangeEquiv f
  have hinj : Function.Injective (fun x : embeddingRange f→β=>x ∘ e) := by
    intro x y h
    funext i
    obtain ⟨j,rfl⟩:=e.surjective i
    exact congrFun h j
  have hh:=entropy_map_injective (map p (fun x=>fun i : embeddingRange f=>x i.val))
    (fun x=>x ∘ e) hinj
  rw [map_comp] at hh
  exact hh

theorem reindexed_deficit_le (p : Law (I→β)) (U : Finset I) (f : J↪I)
    (hf : ∀ j,f j∈U) (hfix : FixedOutside p U) (cap : ℝ)
    (hc : ∀ i∈U,entropy (map p (fun x=>x i))≤cap) :
    Fintype.card J*cap-entropy (map p (fun x=>x ∘ f))≤activeDeficit p U cap := by
  rw [entropy_reindex_range,←embeddingRange_card f]
  apply subset_deficit_le_active p U _ _ hfix cap hc
  intro i hi
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hi
  exact hf j

def selectByContext (p : Law (κ×(I→β))) (f : κ→J→I) : Law (κ×(J→β)) :=
  map p (fun z=>(z.1,z.2 ∘ f z.1))

lemma selectByContext_adaptive (p : Law (κ×(I→β))) (f : κ→J→I) :
    selectByContext p f=adaptiveLaw (first p) (fun c=>map (fiber p c) (fun x=>x ∘ f c)) := by
  apply Law.ext_mean
  intro g
  rw [selectByContext,mean_map,mean_adaptive]
  simp_rw [mean_map]
  have he:=congrArg (fun q=>mean q (fun z=>g (z.1,z.2 ∘ f z.1))) (adaptive_reconstruct p)
  rw [mean_adaptive] at he
  exact he.symm

lemma selectByContext_first (p : Law (κ×(I→β))) (f : κ→J→I) :
    first (selectByContext p f)=first p := by
  rw [selectByContext_adaptive]
  apply Law.ext
  funext c
  simp only [first,adaptiveLaw,←Finset.mul_sum,(map (fiber p c) _).sum_one,mul_one]

lemma selectByContext_fiber (p : Law (κ×(I→β))) (f : κ→J→I)
    (c : κ) (hc : 0<first p c) :
    fiber (selectByContext p f) c=map (fiber p c) (fun x=>x ∘ f c) := by
  rw [selectByContext_adaptive]
  exact fiber_adaptive _ _ _ hc

lemma reindexed_domains (p : Law (I→β)) (D : I→Finset β) (hp : InDomains p D) (f : J→I) :
    InDomains (map p (fun x=>x ∘ f)) (fun j=>D (f j)) := by
  intro y hy j
  obtain ⟨x,hx,rfl⟩:=map_positive _ _ y hy
  exact hp x hx (f j)

theorem selectByContext_deficit (p : Law (κ×(I→β))) (U : κ→Finset I)
    (f : κ→J↪I) (cap : ℝ) (hsel : ∀ c,0<first p c→∀ j,f c j∈U c)
    (hfix : ∀ c,0<first p c→FixedOutside (fiber p c) (U c))
    (hc : ∀ c,0<first p c→∀ i∈U c,entropy (map (fiber p c) (fun x=>x i))≤cap) :
    mean (first (selectByContext p (fun c=>(f c : J→I))))
      (fun c=>Fintype.card J*cap-entropy (fiber (selectByContext p (fun c=>(f c : J→I))) c))≤
      mean (first p) (fun c=>activeDeficit (fiber p c) (U c) cap) := by
  rw [selectByContext_first]
  apply mean_mono_pos
  intro c hp
  rw [selectByContext_fiber _ _ _ hp]
  exact reindexed_deficit_le _ _ _ (hsel c hp) (hfix c hp) cap (hc c hp)

end SharpRamseyFive.FiniteEntropy

end

end OAI
