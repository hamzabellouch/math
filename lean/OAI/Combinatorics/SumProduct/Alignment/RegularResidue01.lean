import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FinitePiece01
import OAI.Combinatorics.SumProduct.Alignment.PolynomialLine01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
namespace RegularBoxPartition

def left (lo hi : ℝ) (M : ℕ) (k : Fin M) : ℝ:=lo+(hi-lo)*k/M
def right (lo hi : ℝ) (M : ℕ) (k : Fin M) : ℝ:=lo+(hi-lo)*(k+1)/M

lemma normalized (lo hi x : ℝ) (hL : lo<hi) (M : ℕ) (hM : 0<M) (k : Fin M) :
    (left lo hi M k≤x ∧ x<right lo hi M k) ↔
      ((k:ℝ)≤(x-lo)/(hi-lo)*M ∧ (x-lo)/(hi-lo)*M<(k:ℝ)+1) := by
  have hMr : 0<(M:ℝ):=by exact_mod_cast hM
  have hLr : 0<hi-lo:=sub_pos.mpr hL
  have h₁ : left lo hi M k≤x ↔ (k:ℝ)≤(x-lo)/(hi-lo)*M:=by
    unfold left
    rw [div_mul_eq_mul_div,le_div_iff₀ hLr]
    constructor
    · intro h
      have hh : (hi-lo)*(k:ℝ)/M≤x-lo:=by linarith
      have ht:=(div_le_iff₀ hMr).mp hh
      nlinarith
    · intro h
      have hh : (hi-lo)*(k:ℝ)/M≤x-lo:=(div_le_iff₀ hMr).mpr (by nlinarith)
      linarith
  have h₂ : x<right lo hi M k ↔ (x-lo)/(hi-lo)*M<(k:ℝ)+1:=by
    unfold right
    rw [div_mul_eq_mul_div,div_lt_iff₀ hLr]
    constructor
    · intro h
      have hh : x-lo<(hi-lo)*((k:ℝ)+1)/M:=by linarith
      have ht:=(lt_div_iff₀ hMr).mp hh
      nlinarith
    · intro h
      have hh : x-lo<(hi-lo)*((k:ℝ)+1)/M:=(lt_div_iff₀ hMr).mpr (by nlinarith)
      linarith
  exact and_congr h₁ h₂

 
theorem one_dimensional (lo hi x : ℝ) (hL : lo<hi) (M : ℕ) (hM : 0<M)
    (hx : lo≤x ∧ x<hi) :
    ∃! k : Fin M,left lo hi M k≤x ∧ x<right lo hi M k := by
  have hMr : 0<(M:ℝ):=by exact_mod_cast hM
  have hLr : 0<hi-lo:=sub_pos.mpr hL
  let y : ℝ:=(x-lo)/(hi-lo)*M
  have hy : 0≤y:=mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) hLr.le) hMr.le
  have hyM : y<(M:ℝ):=by
    have hfrac : (x-lo)/(hi-lo)<1:=(div_lt_one hLr).mpr (by linarith [hx.2])
    simpa only [one_mul] using mul_lt_mul_of_pos_right hfrac hMr
  have hk0 : 0≤⌊y⌋:=Int.floor_nonneg.mpr hy
  have hkM : ⌊y⌋<(M:ℤ):=Int.floor_lt.mpr hyM
  let k : Fin M:=⟨⌊y⌋.toNat,by omega⟩
  have hkc : (k:ℝ)=(⌊y⌋:ℝ):=by dsimp [k]; exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨k,?_,?_⟩
  · dsimp only
    rw [normalized lo hi x hL M hM k,hkc]
    exact ⟨Int.floor_le y,Int.lt_floor_add_one y⟩
  · intro j hj
    have hj':= (normalized lo hi x hL M hM j).mp hj
    have hjfloor : ⌊y⌋=(j:ℤ):=Int.floor_eq_iff.mpr (by simpa [y] using hj')
    apply Fin.ext
    dsimp [k]
    rw [hjfloor]
    simp

lemma endpoints (lo hi : ℝ) (hL : lo<hi) (M : ℕ) (hM : 0<M) (k : Fin M) :
    lo≤left lo hi M k ∧ left lo hi M k<right lo hi M k ∧ right lo hi M k≤hi ∧
      right lo hi M k-left lo hi M k=(hi-lo)/M := by
  have hMr : 0<(M:ℝ):=by exact_mod_cast hM
  have hLr : 0<hi-lo:=sub_pos.mpr hL
  have hk : 0≤(k:ℝ):=by positivity
  have hkM : (k:ℝ)+1≤M:=by exact_mod_cast k.isLt
  have hwidth : right lo hi M k-left lo hi M k=(hi-lo)/M:=by unfold left right; ring
  refine ⟨?_,?_,?_,hwidth⟩
  · unfold left; exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hLr.le hk) hMr.le)
  · have hp : 0<(hi-lo)/(M:ℝ):=div_pos hLr hMr
    linarith
  · have hb : (hi-lo)*((k:ℝ)+1)/M≤hi-lo:=(div_le_iff₀ hMr).mpr
      (mul_le_mul_of_nonneg_left hkM hLr.le)
    unfold right
    linarith

 

theorem multidimensional {ι : Type*} (lo hi x : ι → ℝ)
    (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (hx : ∀ i,lo i≤x i ∧ x i<hi i) :
    ∃! k : ι → Fin M,∀ i,left (lo i) (hi i) M (k i)≤x i ∧
      x i<right (lo i) (hi i) M (k i) := by
  have hh:=fun i=>one_dimensional (lo i) (hi i) (x i) (hL i) M hM (hx i)
  choose k hk hu using hh
  refine ⟨k,hk,?_⟩
  intro j hj
  funext i
  exact hu i (j i) (hj i)

 

theorem fine_partition (C lam : ℝ) (hlam : 0<lam) :
    ∃ M : ℕ,0<M ∧ ∀ Z : ℝ,0<Z → ∀ lo hi : ℝ,lo<hi → hi-lo≤C*Z →
      ∀ k : Fin M,right lo hi M k-left lo hi M k<lam*Z := by
  obtain ⟨M,hM⟩:=exists_nat_gt (max (C/lam) 0)
  have hMpos : 0<M:=by exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hM
  refine ⟨M,hMpos,?_⟩
  intro Z hZ lo hi hL hb k
  rw [(endpoints lo hi hL M hMpos k).2.2.2]
  have hMr : 0<(M:ℝ):=by exact_mod_cast hMpos
  have hB : C<lam*M:=by
    have :=lt_of_le_of_lt (le_max_left _ _) hM
    simpa only [mul_comm] using (div_lt_iff₀ hlam).mp this
  apply (div_lt_iff₀ hMr).mpr
  have :=mul_lt_mul_of_pos_right hB hZ
  nlinarith

end RegularBoxPartition
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RegularResiduePieces
open RoughSamplingWeights RegularBoxPartition FinitePieceAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cell (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (x : ι → ℝ) : ι → Fin M:=
  if hx : ∀ i,lo i≤x i ∧ x i<hi i then
    (multidimensional lo hi x hL M hM hx).choose
  else fun _=>⟨0,hM⟩

omit [DecidableEq ι] in
lemma cell_eq_iff (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (x : ι → ℝ) (hx : ∀ i,lo i≤x i ∧ x i<hi i) (b : ι → Fin M) :
    cell lo hi hL M hM x=b ↔ ∀ i,left (lo i) (hi i) M (b i)≤x i ∧
      x i<right (lo i) (hi i) M (b i) := by
  simp only [cell,dite_eq_left hx]
  have hs:=(multidimensional lo hi x hL M hM hx).choose_spec
  exact ⟨fun h=>h ▸ hs.1,fun h=>(hs.2 b h).symm⟩

def label (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (a : ι → ℤ) (q K : ℕ) (x : ι → ℤ) : (ι → Fin M)×(ι → ZMod K):=
  (cell lo hi hL M hM (fun i=>(a i:ℝ)+q*x i),fun i=>((a i+(q:ℤ)*x i:ℤ):ZMod K))

lemma label_correct (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (a : ι → ℤ) (q K : ℕ) (hq : 0<q) (x : ι → ℤ)
    (hx : x∈boxIndices lo hi (fun i=>(a i:ℝ)) q) (b : ι → Fin M) (u : ι → ZMod K) :
    label lo hi hL M hM a q K x=(b,u) ↔
      (∀ i,left (lo i) (hi i) M (b i)≤(a i:ℝ)+q*x i ∧
       (a i:ℝ)+q*x i<right (lo i) (hi i) M (b i)) ∧
      (∀ i,((a i+(q:ℤ)*x i:ℤ):ZMod K)=u i) := by
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  rw [mem_boxIndices _ _ _ _ hqr] at hx
  simp only [label,Prod.mk.injEq,cell_eq_iff _ _ _ _ _ _ hx,funext_iff]

 

omit [Fintype ι] [DecidableEq ι] in
lemma exists_parameters (a : ι → ℤ) (q K : ℕ) (hh : q.Coprime K) (u : ι → ZMod K) :
    ∃ j : ι → ℤ,∀ i n,(a i+(q:ℤ)*n ≡ (u i).val [ZMOD K]) ↔ n ≡ j i [ZMOD K] := by
  choose j hj using fun i=>residue_parameter q K hh (a i) (u i).val
  exact ⟨j,hj⟩

lemma fiber_eq (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (a : ι → ℤ) (q K : ℕ) (hq : 0<q) (hK : 0<K) [NeZero K]
    (b : ι → Fin M) (u : ι → ZMod K) (j : ι → ℤ)
    (hj : ∀ i n,(a i+(q:ℤ)*n ≡ (u i).val [ZMOD K]) ↔ n ≡ j i [ZMOD K]) :
    fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) (b,u)=
      refinedSet (fun i=>left (lo i) (hi i) M (b i))
        (fun i=>right (lo i) (hi i) M (b i)) (fun i=>(a i:ℝ)) q j K := by
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  ext x
  rw [fiber,Finset.mem_filter,mem_refinedSet _ _ _ _ hqr _ _ hK]
  constructor
  · rintro ⟨hx,he⟩
    obtain ⟨hb,hu⟩:=(label_correct lo hi hL M hM a q K hq x hx b u).mp he
    intro i
    refine ⟨hb i,(hj i (x i)).mp ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hu i
  · intro hx
    have hpar : x∈boxIndices lo hi (fun i=>(a i:ℝ)) q:=by
      rw [mem_boxIndices _ _ _ _ hqr]
      intro i
      have he:=endpoints (lo i) (hi i) (hL i) M hM (b i)
      exact ⟨he.1.trans (hx i).1.1,(hx i).1.2.trans_le he.2.2.1⟩
    refine ⟨hpar,(label_correct lo hi hL M hM a q K hq x hpar b u).mpr ⟨?_,?_⟩⟩
    · exact fun i=>(hx i).1
    · intro i
      have hh:=(ZMod.intCast_eq_intCast_iff _ _ _).mpr ((hj i (x i)).mpr (hx i).2)
      simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hh

lemma weight_eq (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i) (M : ℕ) (hM : 0<M)
    (a : ι → ℤ) (q K : ℕ) (hq : 0<q) (hK : 0<K) [NeZero K]
    (b : ι → Fin M) (u : ι → ZMod K) (j : ι → ℤ)
    (hj : ∀ i n,(a i+(q:ℤ)*n ≡ (u i).val [ZMOD K]) ↔ n ≡ j i [ZMOD K]) :
    weight (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) (b,u)=
      refinedBoxWeight lo hi (fun i=>left (lo i) (hi i) M (b i))
        (fun i=>right (lo i) (hi i) M (b i)) (fun i=>(a i:ℝ)) q j K := by
  rw [weight,fiber_eq lo hi hL M hM a q K hq hK b u j hj,refined_mass _ _ _ _ _ _ _ _ hK]

 

theorem actual_weight_error (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i)
    (M : ℕ) (hM : 0<M) (a b : ι → ℤ) (q t K : ℕ)
    (hq : 0<q) (ht : 0<t) (hK : 0<K) [NeZero K]
    (hqK : q.Coprime K) (htK : t.Coprime K)
    (hsq : ∀ i,4*(q:ℝ)≤hi i-lo i) (hst : ∀ i,4*(t:ℝ)≤hi i-lo i) :
    (∑ z:(ι → Fin M)×(ι → ZMod K),
      |weight (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z-
       weight (boxIndices lo hi (fun i=>(b i:ℝ)) t) (label lo hi hL M hM b t K) z|)≤
      (Fintype.card ((ι → Fin M)×(ι → ZMod K)):ℝ)*
        ((∑ i,8*(q:ℝ)/(hi i-lo i))+(∑ i,8*(t:ℝ)/(hi i-lo i))) := by
  choose ja hja using fun u : ι → ZMod K=>exists_parameters a q K hqK u
  choose jb hjb using fun u : ι → ZMod K=>exists_parameters b t K htK u
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  have htr : 0<(t:ℝ):=by exact_mod_cast ht
  calc
    _≤∑ _z:(ι → Fin M)×(ι → ZMod K),
        ((∑ i,8*(q:ℝ)/(hi i-lo i))+(∑ i,8*(t:ℝ)/(hi i-lo i))):=by
      apply Finset.sum_le_sum
      rintro ⟨v,u⟩ _
      rw [weight_eq lo hi hL M hM a q K hq hK v u (ja u) (hja u),
        weight_eq lo hi hL M hM b t K ht hK v u (jb u) (hjb u)]
      exact compare_refined_box_weights lo hi
        (fun i=>left (lo i) (hi i) M (v i))
        (fun i=>right (lo i) (hi i) M (v i))
        (fun i=>(a i:ℝ)) (fun i=>(b i:ℝ)) q t hqr htr
        (fun i=>(endpoints (lo i) (hi i) (hL i) M hM (v i)).1)
        (fun i=>(endpoints (lo i) (hi i) (hL i) M hM (v i)).2.1.le)
        (fun i=>(endpoints (lo i) (hi i) (hL i) M hM (v i)).2.2.1)
        hsq hst (ja u) (jb u) K hK
    _=_:=by simp [mul_add]

 

theorem select_common_piece (lo hi : ι → ℝ) (hL : ∀ i,lo i<hi i)
    (M : ℕ) (hM : 0<M) (a b : ι → ℤ) (q t K : ℕ)
    (hq : 0<q) (ht : 0<t) (hK : 0<K) [NeZero K]
    (hqK : q.Coprime K) (htK : t.Coprime K)
    (hsq : ∀ i,4*(q:ℝ)≤hi i-lo i) (hst : ∀ i,4*(t:ℝ)≤hi i-lo i)
    (f g : (ι → ℤ) → ℂ) (B : ℝ) (hB : 0≤B)
    (hg : ∀ x∈boxIndices lo hi (fun i=>(b i:ℝ)) t,‖g x‖≤B)
    (η ε : ℝ)
    (hd : η≤‖mean (boxIndices lo hi (fun i=>(a i:ℝ)) q) f-
      mean (boxIndices lo hi (fun i=>(b i:ℝ)) t) g‖)
    (he : B*((Fintype.card ((ι → Fin M)×(ι → ZMod K)):ℝ)*
      ((∑ i,8*(q:ℝ)/(hi i-lo i))+(∑ i,8*(t:ℝ)/(hi i-lo i))))≤ε) :
    ∃ z:(ι → Fin M)×(ι → ZMod K),
      (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z).Nonempty ∧
      η-ε≤‖mean (fiber (boxIndices lo hi (fun i=>(a i:ℝ)) q) (label lo hi hL M hM a q K) z) f-
        mean (fiber (boxIndices lo hi (fun i=>(b i:ℝ)) t) (label lo hi hL M hM b t K) z) g‖ := by
  have hqr : 0<(q:ℝ):=by exact_mod_cast hq
  apply FinitePieceAverages.select _ _ (box_nonempty lo hi _ q hqr hsq)
    (label lo hi hL M hM a q K) (label lo hi hL M hM b t K) f g B hB hg η ε hd
  exact (mul_le_mul_of_nonneg_left
    (actual_weight_error lo hi hL M hM a b q t K hq ht hK hqK htK hsq hst) hB).trans he

end RegularResiduePieces

end
end
end
end

end OAI
