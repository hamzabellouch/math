import Mathlib

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical BigOperators

namespace CriticalPercolation.LinearGrowth
variable {K L T i J : Type*} [Field K] [Field L] [Field T] [Fintype i]

lemma pi_span_map_top (f : K →+* T) (v : J → i → K)
    (hv : Submodule.span K (Set.range v)=⊤) :
    Submodule.span T (Set.range (fun j k => f (v j k)))=⊤ := by
  let P := Submodule.span T (Set.range (fun j k => f (v j k)))
  have hm (x : i → K) : (fun k => f (x k))∈P := by
    have hx : x∈Submodule.span K (Set.range v) := hv ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j,rfl⟩ := hx; exact Submodule.subset_span ⟨j,rfl⟩
    | zero => simpa only [Pi.zero_def,Pi.zero_apply,map_zero] using P.zero_mem
    | add x y hx hy ihx ihy => simpa only [Pi.add_def,Pi.add_apply,map_add] using P.add_mem ihx ihy
    | smul c x hx ih => simpa only [Pi.smul_def,Pi.smul_apply,smul_eq_mul,map_mul] using P.smul_mem (f c) ih
  apply top_unique
  rw [←(Pi.basisFun T i).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨k,rfl⟩
  have he : (Pi.basisFun T i) k=(fun l => f ((Pi.single k (1:K) : i → K) l)) := by
    ext l
    simp [Pi.basisFun_apply,Pi.single_apply]
  rw [he]
  exact hm (Pi.single k 1)

lemma pi_span_descends (f : L →+* T) (w : J → i → L)
    (hw : Submodule.span T (Set.range (fun j k => f (w j k)))=⊤) :
    Submodule.span L (Set.range w)=⊤ := by
  by_contra hn
  obtain ⟨φ,hφ,hker⟩ := (Submodule.span L (Set.range w)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
  let c (k : i) := φ (Pi.single k 1)
  have hφsum (x : i → L) : φ x=∑ k, x k*c k := by
    conv_lhs => rw [←(Pi.basisFun L i).sum_repr x]
    simp [c,Pi.basisFun_apply,Pi.basisFun_repr, map_sum,map_smul,smul_eq_mul]
  let ψ : (i → T) →ₗ[T] T := {
    toFun x := ∑ k, x k*f (c k)
    map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
    map_smul' a x := by simp [smul_eq_mul,Finset.mul_sum,mul_assoc] }
  have hker' : Submodule.span T (Set.range (fun j k => f (w j k)))≤ψ.ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨j,rfl⟩
    change (∑ k, f (w j k)*f (c k))=0
    simp_rw [←map_mul]
    rw [←map_sum,←hφsum]
    have he : φ (w j)=0 := hker (Submodule.subset_span ⟨j,rfl⟩)
    rw [he,map_zero]
  have hψ : ψ=0 := LinearMap.ker_eq_top.mp (top_unique (hw ▸ hker'))
  apply hφ
  apply LinearMap.ext
  intro x
  change φ x=0
  rw [hφsum]
  apply Finset.sum_eq_zero
  intro k hk
  have he := congrArg (fun a : (i → T) →ₗ[T] T => a (Pi.single k 1)) hψ
  have hc : c k=0 := f.injective (by simpa [ψ,Pi.single_apply] using he)
  rw [hc,mul_zero]

lemma pi_span_transfer (f : K →+* T) (e : L →+* T)
    (v : J → i → K) (w : J → i → L)
    (hm : ∀ j k, f (v j k)=e (w j k))
    (hv : Submodule.span K (Set.range v)=⊤) : Submodule.span L (Set.range w)=⊤ := by
  apply pi_span_descends e w
  simpa only [hm] using pi_span_map_top f v hv

end CriticalPercolation.LinearGrowth
end
end

end OAI
