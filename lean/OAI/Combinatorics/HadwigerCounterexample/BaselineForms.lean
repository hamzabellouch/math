import OAI.Combinatorics.HadwigerCounterexample.BaselineExtension

namespace OAI

/-! # Baseline Forms -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix
variable {p : Shape} {n N : ℕ}

def lowCross (K : ℕ) (B : Cross p n) :=
  ∀ z i,( (B z)ᵀ * IP p n i).rank ≤ K

def fitsTable (a b : Plan p n) (B T : Cross p n) :=
  ∀ z, ∀ x∈tabSpace a z,∀ y∈tabSpace b (flipZ p z), evmat (B z) x y=evmat (T z) x y

theorem fits_recip {B T : Cross p n} {a b : Plan p n} (h : fitsTable a b B T) :
    fitsTable b a (reciprocal p B) (reciprocal p T) := by
  intro z x hx y hy
  have hx' : x∈tabSpace b (flipZ p (flipZ p z)) := by rwa [flipZ_flip]
  change evmat _ _ _=evmat _ _ _
  unfold reciprocal
  rw [evmat_transpose,evmat_transpose,h _ y hy x hx']

def blin (K : ℕ) := 4*K+56

set_option maxHeartbeats 800000 in
theorem start_form (a b : Pin p n N) (x y : UnitType p n N) (T : Cross p n)
    (ka kb : Plan p n)
    (hA : ∀ z,ka z≤primal p n) (hB : ∀ z,kb z≤primal p n)
    (hd : ∀ z, Disjoint (tabSpace a.sp z) (ka z))
    (hd' : ∀ z, Disjoint (tabSpace b.sp z) (kb z))
    (ha : a.agree x) (hb : b.agree y) (h1 : tableFlag a b T x)
    (h2 : tableFlag b a (reciprocal p T) y)
    (K : ℕ) (hk : planRank a.sp ≤ K) (hk' : planRank b.sp ≤ K)
    (hv : ∀ z, dim (ka z) ≤ 28) (hv' : ∀ z, dim (kb z) ≤ 28) :
    ∃ M : Cross p n, fitsTable a.sp b.sp M T ∧
      rowAgree (a.sp ⊔ ka) M (actual p x y) ∧
      rowAgree (b.sp ⊔ kb) (reciprocal p M) (actual p y x) ∧
      lowCross (blin K) M ∧ lowCross (blin K) (reciprocal p M) := by
  let A := actual p x y
  have hh (z : Place p) (u v) (hu : u∈tabSpace a.sp z) (hv : v∈tabSpace b.sp (flipZ p z))
      (h : u∈a.sp z ∨ v∈b.sp (flipZ p z)) : evmat (A z) u v=evmat (T z) u v := by
    rcases h with h|h
    · have h' : u ∈ a.sp (flipZ p (flipZ p z)) := by rwa [flipZ_flip]
      have he := h2 _ v hv u h'
      have hf := flag_actual (a:=b) y x ha (flipZ p z) v hv u h'
      have hg := hf.trans he.symm
      rw [← reciprocal_actual x y] at hg
      simp only [reciprocal,flipZ_flip,evmat_transpose] at hg
      exact hg
    exact (flag_actual (a:=a) x y hb _ u hu v h).trans (h1 _ u hu v h).symm
  choose M hC hD hE hF using fun z =>
    base_pair a.sp b.sp z (flipZ p z) (ka z) (kb (flipZ p z)) (hA _) (hB _) (hd _) (hd' _)
      (A z) (T z) (fun u hu v hv g => hh z u v hu hv g)
  have hr (z) {a s : Plan p n} (h : planRank a≤K) (hg : ∀ z,dim (s z)≤28) :
      dim (a z ⊔ s z : Submodule _ _) ≤ K+28 :=
    (Submodule.finrank_add_le_finrank_add_finrank ..).trans
      (Nat.add_le_add ((dim_le_plan a _).trans h) (hg _))
  have hm z {L} (hl : L≤K) : dim (a.sp z ⊔ ka z : Submodule _ _)+
      dim (b.sp (flipZ p z) ⊔ kb (flipZ p z):Submodule _ _)+2*L ≤ blin K := by
    apply le_trans (Nat.add_le_add (Nat.add_le_add (hr z hk hv) (hr _ hk' hv'))
      (Nat.mul_le_mul_left 2 hl))
    unfold blin; omega
  refine ⟨M,hC,(fun z u hu v => hD z u v (Or.inl hu)),?_,
    fun z i => (hE z i).trans (hm z hk),?_⟩
  · rw [← reciprocal_actual x y]
    intro z v hv u
    unfold reciprocal; rw [evmat_transpose,evmat_transpose]
    apply hD
    right
    rw [flipZ_flip]; exact hv
  intro z i
  unfold reciprocal; rw [transpose_transpose]
  exact (hF (flipZ p z) i).trans (hm _ hk')

theorem channel_eval (p : Shape) {n} (M : Cross p n) (j : Bool) (z : Place p)
    (x : Dir p n) (y : Vec (Chan p)) :
    dotProduct y (channelOut p M j z *ᵥ x)=evmat (M z) x (IH p n j *ᵥ y) := by
  unfold channelOut evmat
  rw [dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]

theorem channel_same {M T : Cross p n} (i z u)
    (h : ∀ v : Vec (Chan p), evmat (M z) u (IH p n i *ᵥ v)=evmat (T z) u (IH p n i *ᵥ v)) :
    channelOut p M i z *ᵥ u = channelOut p T i z *ᵥ u := by
  classical
  funext j
  have he v : dotProduct v (channelOut p M i z *ᵥ u)=dotProduct v (channelOut p T i z*ᵥ u) := by
    rw [channel_eval, channel_eval, h]
  simpa using he (Pi.single j 1)

theorem fits_channel {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (z : Place p) (x : Dir p n) (hx : x∈tabSpace a z) (j : Bool) :
    channelOut p M j z *ᵥ x = channelOut p T j z *ᵥ x := by
  apply channel_same j
  intro v
  exact h z x hx _ (channel_le_table b _ j ⟨_,rfl⟩)

theorem fits_inj {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (ht : tableInj a b T) : tableInj a b M := by
  intro z i j v hv hh
  apply ht z i j v hv
  rwa [fits_channel h z _ (pin_le_table a z hv) j] at hh

private theorem cout_ev (A B : Mat (Chan p) (JointIdx p n)) (x y) :
    evmat (Aᵀ*B) x y=dotProduct (A *ᵥ x) (B *ᵥ y) := by
  rw [evmat,← mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]

theorem fits_contract {M T : Cross p n} {a b : Plan p n} (h : fitsTable a b M T)
    (i j : Bool) (x : Profile p n) (hx : x ∈ effective a i) :
    contract p M i j x=contract p T i j x := by
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  apply (box_eval_iff (tabSpace a (e,true)) (tabSpace a (e,false)) _ _).mp ?_ _
  · have hp := lift_mem_box (IP p n i) (IP p n i) ((effective_mem.mp hx).2 e)
    exact box_le (le_trans le_sup_left (half_le_table a _ i))
      (le_trans le_sup_left (half_le_table a _ i)) hp
  intro x hx y hy; rw [cout_ev, cout_ev,fits_channel h _ _ hx,fits_channel h _ _ hy]

variable {I : Type} [Fintype I]

theorem frozen_contract_key {M T : Cross p n} {a} (v : Volley p n I) (t : Tagging p I)
    (h : rowAgree (a⊔v.keyPlan t) M T) (i : I) (j : Bool) :
    contract p M (v.obj i) j (v.atomAt t i)=contract p T (v.obj i) j (v.atomAt t i) := by
  classical
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : inc e (t i)
  · have hx b :
        v.rayLoc i ∈ (v.keyPlan t (e,b)) := colSp_mem (P:=v.keyM t e)
          (⟨i,he⟩ : Volley.visits p t e)
    have hE (b : Bool) : channelOut p M j (e,b) *ᵥ v.rayLoc i =
        channelOut p T j (e,b) *ᵥ v.rayLoc i :=
      channel_same j _ _ (fun y => h _ _ (Submodule.mem_sup_right (hx b)) _)
    simp only [Volley.atomAt,atom_def,he, ite_true,mom,liftM_outer,mpair_outer]
    rw [cout_ev,cout_ev]
    exact congrArg₂ dotProduct (hE true) (hE false)
  simp only [Volley.atomAt,atom_def,he,ite_false,map_zero]

end HadwigerCounterexample

end

end OAI
