import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace ENNReal

namespace Kadison.InfiniteAmplification

variable {ι : Type*}

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev Space (ι H : Type*) [NormedAddCommGroup H] := lp (fun _ : ι => H) 2

omit [CompleteSpace H] [CompleteSpace G] in
lemma map_mem (T : H →L[ℂ] G) (x : Space ι H) : Memℓp (fun i => T (x i)) 2 := by
  apply ((lp.memℓp x).norm.const_smul ‖T‖).mono
  intro i
  exact T.le_opNorm (x i)

def mapLinear (T : H →L[ℂ] G) : Space ι H →ₗ[ℂ] Space ι G where
  toFun x := ⟨fun i => T (x i),map_mem T x⟩
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' c x := by ext i; exact map_smul _ _ _

omit [CompleteSpace H] [CompleteSpace G] in
lemma norm_mapLinear_le (T : H →L[ℂ] G) (x : Space ι H) :
    ‖mapLinear T x‖≤‖T‖*‖x‖ := by
  calc
    _≤‖(‖T‖:ℂ) • x‖ := lp.norm_mono (by norm_num) (by
      intro i
      change ‖T (x i)‖≤‖(‖T‖:ℂ) • x i‖
      simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg T)] using T.le_opNorm (x i))
    _=_ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg T)]

def map (T : H →L[ℂ] G) : Space ι H →L[ℂ] Space ι G :=
  (mapLinear T).mkContinuous ‖T‖ (norm_mapLinear_le T)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma map_apply (T : H →L[ℂ] G) (x : Space ι H) (i : ι) : map T x i=T (x i) := rfl

lemma map_adjoint (T : H →L[ℂ] G) : (map (ι:=ι) T).adjoint=map T.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum,map_apply,ContinuousLinearMap.adjoint_inner_left]

def diagonal : (H →L[ℂ] H) →⋆ₐ[ℂ] (Space ι H →L[ℂ] Space ι H) where
  toFun := map
  map_one' := by ext x i; rfl
  map_zero' := by ext x i; rfl
  map_add' a b := by ext x i; rfl
  map_mul' a b := by ext x i; rfl
  commutes' c := by ext x i; rfl
  map_star' a := (map_adjoint a).symm

@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : Space ι H) (i : ι) : (diagonal (ι:=ι) (H:=H)) T x i=T (x i) := rfl

def mapIsometry (V : H →ₗᵢ[ℂ] G) : Space ι H →ₗᵢ[ℂ] Space ι G where
  toLinearMap := (map V.toContinuousLinearMap).toLinearMap
  norm_map' x := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (fun i => (V.norm_map (x i)).le)
    · exact lp.norm_mono (by norm_num) (fun i => (V.norm_map (x i)).ge)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma mapIsometry_apply (V : H →ₗᵢ[ℂ] G) (x : Space ι H) (i : ι) :
    mapIsometry V x i=V (x i) := rfl

end Kadison.InfiniteAmplification

end

end
end

end OAI
