import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BadClientWeighted

namespace OAI

namespace MetricKMedianRecovery.LocalSearch

variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq U]

omit [Fintype U] in
lemma exchange_add_nonempty (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U)
    (he : 0 < exchangeWeight psi slot e) : (exchangeAdd psi e).Nonempty := by
  cases e with
  | inl u =>
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · exact Finset.card_pos.mp h.1
    · norm_num at he
  | inr bs => obtain ⟨b,s⟩ := bs; exact Finset.singleton_nonempty b

end MetricKMedianRecovery.LocalSearch
namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma mem_subtype_map (T : Finset V) (A : Finset ↥T) (x : ↥T) :
    x.val ∈ A.map (Function.Embedding.subtype _) ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y,hy,hxy⟩ := Finset.mem_map.mp h
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro h; exact Finset.mem_map.mpr ⟨x,h,rfl⟩

theorem protected_swap_sum (F D S Ob Og : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (hbf : Ob ⊆ F)
    (hcard : Ob.card + Og.card ≤ S.card) (assign proxy : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ Ob ∨ assign p ∈ Og)
    (hproxy : ∀ i ∈ Og, proxy i ∈ S) (hinj : Set.InjOn proxy Og) :
    0 ≤ ∑ p ∈ D, if assign p ∈ Ob then (1+2*(6/5:ℝ))*dist p (assign p)-connection S p
      else (6/5:ℝ)*(dist p (proxy (assign p))-connection S p) := by
  classical
  by_cases hb : Ob.Nonempty
  swap
  · have hempty : Ob = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
    apply Finset.sum_nonneg
    intro p hp
    have hg : assign p ∈ Og := (hassign p hp).resolve_left (by simp [hempty])
    simp only [hempty,Finset.notMem_empty,ite_false]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (connection_le (hproxy _ hg)))
  let Phi := Og.image proxy
  have hPhiS : Phi ⊆ S := by
    rintro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact hproxy i hi
  have hPhicard : Phi.card = Og.card := Finset.card_image_iff.mpr hinj
  let Uf := S \ Phi
  have hBU : Ob.card ≤ Uf.card := by
    dsimp [Uf]
    rw [Finset.card_sdiff_of_subset hPhiS,hPhicard]
    omega
  have hUne : Uf.Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hb).trans_le hBU)
  let B := ↥Ob
  let U := ↥Uf
  let u0 : U := ⟨hUne.choose,hUne.choose_spec⟩
  let psi : B → U := fun b =>
    if h : nearest S hS b.val ∈ Uf then ⟨nearest S hS b.val,h⟩ else u0
  have hpsi (b : B) (hn : nearest S hS b.val ∉ Phi) :
      (psi b).val = nearest S hS b.val := by
    have hnU : nearest S hS b.val ∈ Uf := Finset.mem_sdiff.mpr ⟨nearest_mem S hS _,hn⟩
    simp only [psi,dite_eq_left hnU]
  obtain ⟨slot,hslot⟩ := slot_allocation psi (by simpa [B,U] using hBU)
  let R : ExchangeIndex B U → Finset V := fun e =>
    (exchangeRemove psi slot e).map (Function.Embedding.subtype _)
  let A : ExchangeIndex B U → Finset V := fun e =>
    (exchangeAdd psi e).map (Function.Embedding.subtype _)
  let w := exchangeWeight psi slot
  have hRU (e) : R e ⊆ Uf := by
    intro s hs
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hs
    exact u.property
  have hAB (e) : A e ⊆ Ob := by
    intro i hi
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hi
    exact b.property
  have hRm (e) (s : U) : s.val ∈ R e ↔ s ∈ exchangeRemove psi slot e :=
    mem_subtype_map Uf _ s
  have hAm (e) (b : B) : b.val ∈ A e ↔ b ∈ exchangeAdd psi e :=
    mem_subtype_map Ob _ b
  apply weighted_swap_family F D S Ob Og hS hSF hlocal assign proxy hassign hproxy
    R A w (6/5) (exchangeWeight_nonneg psi slot)
  · intro e he
    obtain ⟨hce,hwidth⟩ := exchange_width psi slot e he
    refine ⟨(hRU e).trans Finset.sdiff_subset,(hAB e).trans hbf,?_,?_,?_,?_⟩
    · exact (exchange_add_nonempty psi slot e he).map
    · simpa only [R,A,Finset.card_map] using hce.symm.le
    · simpa only [R,Finset.card_map,hce] using hwidth
    · simpa only [A,Finset.card_map] using hwidth
  · intro i hi
    have hm : ∀ e, i ∈ A e ↔ (⟨i,hi⟩ : B) ∈ exchangeAdd psi e :=
      fun e => hAm e ⟨i,hi⟩
    simp_rw [hm]
    exact total_addition_weight psi slot hslot ⟨i,hi⟩
  · intro s _
    by_cases hs : s ∈ Uf
    · have hm : ∀ e, s ∈ R e ↔ (⟨s,hs⟩ : U) ∈ exchangeRemove psi slot e :=
        fun e => hRm e ⟨s,hs⟩
      simp_rw [hm]
      exact removal_weight_le psi slot ⟨s,hs⟩
    · have hm : ∀ e, s ∉ R e := fun e h => hs (hRU e h)
      simp only [hm,ite_false,Finset.sum_const_zero]
      norm_num
  · intro e _ i hi hr
    exact (Finset.mem_sdiff.mp (hRU e hr)).2 (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  · intro e he i hi hia hr
    have hn : nearest S hS i ∉ Phi := (Finset.mem_sdiff.mp (hRU e hr)).2
    let b : B := ⟨i,hi⟩
    have hnA : b ∉ exchangeAdd psi e := fun h => hia ((hAm e b).mpr h)
    have hmem : psi b ∈ exchangeRemove psi slot e := (hRm e (psi b)).mp (hpsi b hn ▸ hr)
    exact exchange_preserves_image psi slot hslot e he b hnA hmem

theorem protected_swap_bound (F D S Ob Og : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (hbf : Ob ⊆ F)
    (hcard : Ob.card + Og.card ≤ S.card) (assign proxy : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ Ob ∨ assign p ∈ Og)
    (hproxy : ∀ i ∈ Og, proxy i ∈ S) (hinj : Set.InjOn proxy Og) :
    (∑ p ∈ D.filter (fun p => assign p ∈ Ob), connection S p) +
      (6/5:ℝ)*(∑ p ∈ D.filter (fun p => assign p ∉ Ob), connection S p) ≤
      (1+2*(6/5:ℝ))*(∑ p ∈ D.filter (fun p => assign p ∈ Ob), dist p (assign p)) +
      (6/5:ℝ)*(∑ p ∈ D.filter (fun p => assign p ∉ Ob), dist p (proxy (assign p))) :=
  weighted_swap_sum_form D S Ob assign proxy (6/5)
    (protected_swap_sum F D S Ob Og hS hSF hlocal hbf hcard assign proxy hassign hproxy hinj)

end MetricKMedianRecovery.LocalSearch

end OAI
