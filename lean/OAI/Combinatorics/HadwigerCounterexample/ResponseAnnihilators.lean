import OAI.Combinatorics.HadwigerCounterexample.FrozenProjections

namespace OAI

/-! # Response Annihilators -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I : Type} [Fintype I]

def dotL (x : Vec I) : Vec I →ₗ[F] F where
  toFun y := dotProduct x y
  map_add' u v := dotProduct_add x _ _
  map_smul' b u := by
    simp only [dotProduct,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_sum,mul_left_comm]

theorem dotL_surj (x : Vec I →ₗ[F] F) : ∃ y : Vec I,x=dotL y := by
  classical
  let y (i:I) := x (Pi.single i 1)
  refine ⟨y,LinearMap.ext fun v => ?_⟩
  have he : x v=x (∑ i, Pi.single i (v i)) := by rw [Finset.univ_sum_single]
  rw [he,map_sum]
  change (∑ i,x (Pi.single i (v i)))=∑ i,y i*v i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (v i)=v i • (Pi.single i 1 : Vec I) from (by
    funext j
    by_cases h : j = i
    · simp [h]
    simp [Pi.single_eq_of_ne h]),
    map_smul]
  exact mul_comm _ _

private theorem protection_test {S : Space (Ray p n)} {q} {E L : Finset (Label p.b)}
    (h : protectedBy p S q E) {s} (hs : s∈L) (he : s∉E) (hl : L.card≤q)
    (ψ : Vec (AIdx p.g n)) :
    ∃ x ∈ annih S,∀ j∈L,(labMat p n j)ᵀ *ᵥ x= if j=s then ψ else 0 := by
  classical
  let P := S.subtype.coprod (labcomb p n L)
  let Q := dotL ψ ∘ₗ LinearMap.proj s ∘ₗ (LinearMap.snd F S (LabVals p n))
  obtain ⟨f,hf⟩ : ∃ f,f ∘ₗ P=Q := by
    refine HadwigerCounterexample.mem_range_comp (show LinearMap.ker P≤LinearMap.ker Q from ?_)
    rintro ⟨w,z⟩ hw
    change w.val + labcomb p n L z=0 at hw
    have hb : labcomb p n L z ∈ S := by
      rw [show labcomb p n L z=w.val from add_left_cancel (hw.trans (char_two w.val).symm)]
      exact w.property
    change dotProduct ψ (z s)=0
    rw [h L z hb hl s hs he,dotProduct_zero]
  obtain ⟨x,rfl⟩ := dotL_surj f
  refine ⟨x,?_,fun j hj => ?_⟩
  · rw [annih_mem]; intro y hy
    have hh := LinearMap.congr_fun hf (⟨y,hy⟩,0)
    change dotProduct x (y+labcomb p n L 0)=dotProduct ψ 0 at hh
    rw [map_zero,add_zero,dotProduct_zero] at hh
    exact hh
  have h1 (z : Vec (AIdx p.g n)) : dotProduct z ((labMat p n j)ᵀ *ᵥ x)=
      if j=s then dotProduct ψ z else 0 := by
    let y : LabVals p n := Pi.single j z
    have hh := LinearMap.congr_fun hf (0,y)
    change dotProduct x (0+labcomb p n L y)=dotProduct ψ (y s) at hh
    have hh' : labcomb p n L y = putLab p n j z := by
      rw [labcomb_eval,Finset.sum_eq_single j]
      · simp [y]
      · intro k _ hk; simp [y,Pi.single_eq_of_ne hk]
      simp [hj]
    rw [dotProduct_transpose_mulVec,labMat_act]
    rw [zero_add,hh'] at hh
    rw [hh]
    by_cases h : j = s
    · simp [y,h]
    simp [y,h]
  funext i
  have h2 := h1 (Pi.single i 1)
  by_cases hh : j = s
  · simpa only [hh,ite_true,dotProduct_single,single_dotProduct,mul_one,one_mul] using h2
  simpa only [ite_eq_right hh,Pi.zero_apply,single_dotProduct,one_mul] using h2

namespace Volley
variable {v : Volley p n I}

private theorem mark_test {w : I → Bool} (hb : v.bounded w)
    (t : Tagging p I) {a : Plan p n} {q} (hv : v.avoids a q)
    (j : I) (z : Place p) (L : Finset (Label p.b)) (hl : L.card+14 ≤ q)
    (ψ : Vec (AIdx p.g n))
    (hh : inc z.1 (t j) → dotProduct ψ (baseV (v.par j)) = 0) :
    ∃ x ∈ annih (sPin (v.frozen a t) z (v.obj j)),∀ k∈L,(labMat p n k)ᵀ *ᵥ x=
      if k=v.sel j then ψ else 0 := by
  classical
  let i := v.obj j
  obtain ⟨B,hB,hj,hc,hsel⟩ := hv i
  let T := L∪v.marked i
  have hT : T.card ≤ q :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add_left (v.marked_card hb i) L.card).trans hl)
  have hjj : j ∈ v.here i := by simp [here,i]
  obtain ⟨x,hx,hX⟩ := protection_test (L:=T) (hB z)
    (mem_union_right L (v.marked_mem j)) (hj _ hjj) hT ψ
  refine ⟨x, ?_, fun k hk => hX k (mem_union_left _ hk)⟩
  have he : sPin (v.frozen a t) z i ≤ LinearMap.ker (dotL x) := by
    rw [v.sPin_frozen]
    refine sup_le (fun y hy => (annih_mem ..).mp hx y hy) ?_
    rintro y ⟨y,⟨u,rfl⟩,rfl⟩
    rw [LinearMap.mem_ker]
    rw [mulVecLin_apply,mulVecLin_apply,v.key_proj,map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [map_smul]
    suffices h : dotL x (v.rayAt k.val)=0 by rw [h,smul_zero]
    change dotProduct x (point p (v.sel k.val) (v.par k.val))= _
    have hh' : k.val ∈ v.here i := (v.visitH_here ..).mp hk
    have hx' : v.sel k.val ∈ T := mem_union_right _ (Finset.mem_image_of_mem _ hh')
    rw [point,←labMat_act, ←dotProduct_transpose_mulVec,hX _ hx']
    by_cases h : v.sel k.val=v.sel j
    · have he' : k.val=j := hsel hh' hjj h
      rw [ite_eq_left h,dotProduct_comm,he']
      exact hh (he' ▸ k.property)
    rw [ite_eq_right h,dotProduct_zero]
  rw [annih_mem]
  exact fun y hy => he hy

private theorem ev_mput (s : Label p.b) (M : BaseMat p n) (x y : Ray p n) :
    evmat (mput p s M) x y = evmat M ((labMat p n s)ᵀ *ᵥ x) ((labMat p n s)ᵀ *ᵥ y) := by
  rw [← evmat_pull]
  unfold mput pullM
  rw [transpose_transpose]

/-- Diagnostic for the two quotients by one affine ray. -/
private theorem mark_diag {J : Type} [Fintype J] (Z : Mat (Option J) (Option J))
    (hZ : Zᵀ = Z) (hd : ∀ i,Z i i=Z none i) (v : Vec (Option J))
    (hv : v none=1) (he : ∀ φ, dotProduct φ v = 0 → ∀ ψ, dotProduct ψ v = 0 →
      evmat Z φ ψ=0) :
    Z = (Z none none) • vecMulVec v v := by
  classical
  let θ (i : Option J) := Pi.single i 1 + (Pi.single none (v i) : Vec (Option J))
  have hθ (i) : dotProduct (θ i) v=0 := by
    rw [show θ i=_+_ from rfl,add_dotProduct,single_dotProduct,single_dotProduct,
      hv,one_mul,mul_one,char_two]
  have hg (i j : Option J) :
      Z i j + Z i none * v j + (v i*(Z none j)+v i * (Z none none * v j)) = 0 := by

    have hh := he _ (hθ i) _ (hθ j)
    simp only [θ,evmat,Matrix.mulVec_add,add_dotProduct,dotProduct_add, single_dotProduct,Matrix.mulVec_single,op_smul_eq_smul, one_mul,one_smul,Pi.smul_apply,smul_eq_mul,col_apply] at hh
    simpa only [mul_comm,mul_left_comm,mul_assoc,add_comm,add_left_comm,add_assoc] using hh
  have hf i : Z i none=Z none i := congr_fun (congr_fun hZ none) i
  have h0 (i : Option J) : Z none i=Z none none * v i := by
    have h := hg i i
    rw [hd i,hf,mul_comm (Z none i),show v i*(Z none none*v i)=Z none none*v i from
      (by rw [mul_left_comm,bit_sq])] at h
    have h' : Z none i+Z none none*v i=0 := calc
      _ = Z none i + ((v i * Z none i+v i * Z none i)+Z none none*v i) := by rw [char_two,zero_add]
      _ = 0 := (by simpa only [add_assoc] using h)
    exact add_right_cancel (h'.trans (char_two _).symm)
  ext i j
  change Z i j=Z none none*(v i*v j)
  have h := hg i j
  rw [h0 j,char_two,add_zero,hf,h0, mul_assoc] at h
  exact add_right_cancel (h.trans (char_two _).symm)

set_option maxHeartbeats 600000 in
theorem mark_atom {w : I → Bool} (hb : v.bounded w)
    (t : Tagging p I) {a : Plan p n} {q} (hv : v.avoids a q)
    (j : I) (e : Comp p.g)
    (L : Finset (Label p.b)) (hl : L.card+14≤q)
    (Z : Label p.b → BaseMat p n)
    (ht : ∀ s,s∉L → Z s=0) (hh : ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i)
    (hg : vanish (sPin (v.frozen a t) (e,true) (v.obj j))
      (sPin (v.frozen a t) (e,false) (v.obj j)) (labelSum p L Z)) :
    Z (v.sel j) = if inc e (t j) then
      Z (v.sel j) none none • vecMulVec (baseV (v.par j)) (baseV (v.par j)) else 0 := by
  classical
  let s := v.sel j
  change Z s = if inc e (t j) then _ else _
  by_cases hs : s∈L
  · let y := baseV (v.par j)
    have he (φ ψ : Vec (AIdx p.g n)) (hφ : inc e (t j) → dotProduct φ y=0)
        (hψ : inc e (t j) → dotProduct ψ y=0) :
        evmat (Z s) φ ψ=0 := by
      obtain ⟨x,hx,hX⟩ := mark_test hb t hv j (e,true) L hl φ hφ
      obtain ⟨y,hy,hY⟩ := mark_test hb t hv j (e,false) L hl ψ hψ
      have h := hg x hx y hy
      unfold labelSum at h
      rw [←mpair_outer,mpair_sum,Finset.sum_eq_single s] at h
      · rwa [mpair_outer,ev_mput,hX _ hs,hY _ hs,ite_eq_left rfl,ite_eq_left rfl] at h
      · intro i hi he; rw [mpair_outer,ev_mput,hX _ hi,hY _ hi,ite_eq_right he,ite_eq_right he]
        simp [evmat]
      simp [hs]
    by_cases h : inc e (t j)
    · rw [ite_eq_left h]
      exact mark_diag _ (hh s hs).1 (hh s hs).2 y rfl (fun φ hφ ψ hψ => he φ ψ (fun _ => hφ)
        (fun _ => hψ))
    rw [ite_eq_right h]
    apply evmat_ext
    intro φ ψ
    rw [he φ ψ (fun e => (h e).elim) (fun e => (h e).elim)]
    simp [evmat]
  change Z s = if inc e (t j) then Z s none none • _ else _
  rw [ht s hs]
  simp

end Volley
end HadwigerCounterexample

end

end OAI
