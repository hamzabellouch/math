import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Slice
import OAI.Probability.LogConcave.JetEstimates.SmoothTensorCurve
import OAI.Probability.LogConcave.Sampling.NormalizedTensorMajorantScale
import OAI.Probability.LogConcave.Sampling.SpatialTransport

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function
open scoped NNReal BigOperators

namespace TensorEnergy
lemma multilinearTensor_const_smul {d n : ℕ} (a : ℝ)
    (f : Point d → Point d) (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) :
    multilinearTensor (iteratedFDeriv ℝ n (fun z => a • f z) y)=
      fun c => a*multilinearTensor (iteratedFDeriv ℝ n f y) c := by
  funext c
  rw [iteratedFDeriv_const_smul_apply' (hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)))]
  simp [multilinearTensor,real_inner_smul_right]
end TensorEnergy

lemma probabilityVelocity_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (probabilityVelocity F x r ρ) y))
      (normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hh := (conditionalMean_iterated_uniform_split hF x hr hlam hl hρ0 hρ1 hR ha y (n:=n)).abs_const_mul (-r)
  rw [←TensorEnergy.multilinearTensor_const_smul (-r) _
    (conditionalFieldMean_smooth hF x hr.le hl hρ0 hρ1)] at hh
  change TensorEnergy.AllSplitBound _ _ at hh
  apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _)) (pow_nonneg hR.le _)))
  rw [abs_neg,abs_of_pos hr]
  have hC := normalizedTensorMajorant_nonneg (n+1) 1
  have he : r*((lam:ℝ)*r*normalizedTensorMajorant (n+1) 1/R^(n-1))=
      ((lam:ℝ)*r^2)*(normalizedTensorMajorant (n+1) 1/R^(n-1)) := by ring
  rw [he]
  exact mul_le_of_le_one_left (by positivity) (by linarith)

theorem probabilityTransport_iterated_split (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(d : ℕ) (F : Point d → ℝ) (lam : ℝ≥0)
      (hF : Primitive F lam) (x : Point d) (r R T : ℝ)
      (hr : 0<r) (_ : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
      (_ : 0<R) (_ : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
      (s t : Icc (0:ℝ) T) (y : Point d),
      TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n
        (probabilityTransport hF x hr.le hl hT0 hT1 s t) y)) (C/R^(n-1)) := by
  obtain ⟨C,hC,hbound⟩ := TensorEnergy.smoothTensorCurve_bounds
    (fun k => normalizedTensorMajorant (k+1) 1)
    (fun k => normalizedTensorMajorant_nonneg _ _) n
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 s t y
  let a : ℝ := (t:ℝ)-(s:ℝ)
  let q (u : ℝ) := (s:ℝ)+a*u
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc 0 T := by
    dsimp [q,a]
    constructor
    · nlinarith [s.2.1,t.2.1,mul_nonneg s.2.1 (sub_nonneg.mpr hu.2),mul_nonneg t.2.1 hu.1]
    · nlinarith [s.2.2,t.2.2,mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hu.2),
        mul_nonneg (sub_nonneg.mpr t.2.2) hu.1]
  have ha : |a|≤1 := (abs_le).mpr ⟨by dsimp [a]; linarith [t.2.1,s.2.2],by dsimp [a]; linarith [t.2.2,s.2.1]⟩
  let X (p : ℝ × Point d) := spatialTransport hF x hr.le hl hT0 hT1 s (q p.1,p.2)
  let V (u : ℝ) (z : Point d) := a • probabilityVelocity F x r (q u) z
  have hVX : TensorEnergy.SmoothTensorCurve d (fun k => normalizedTensorMajorant (k+1) 1) R 1 X V := by
    constructor
    · exact (spatialTransport_smooth hF x hr.le hl hT0 hT1 s).comp
        ((contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd)
    · intro z
      dsimp [X,q]
      simp only [mul_zero,add_zero]
      exact spatialTransport_initial hF x hr.le hl hT0 hT1 s z
    · intro u hu z
      have hd := (spatialTransport_deriv hF x hr.le hl hT0 hT1 s (hq u hu) z).scomp u
        ((hasDerivAt_const u (s:ℝ)).add ((hasDerivAt_const u a).mul (hasDerivAt_id u)))
      simpa only [zero_mul,one_mul,mul_one,zero_add,X,V,q,Function.comp_def] using hd
    · intro u hu
      exact (contDiff_const (c:=a)).smul ((contDiff_const (c:=(-r:ℝ))).smul
        (conditionalFieldMean_smooth hF x hr.le hl (hq u hu).1 ((hq u hu).2.trans_lt hT1)))
    · intro k u hu z
      have huT := hq u hu
      have hρ : R^2≤1-(q u)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr huT.2) (add_nonneg hT0 huT.1)]
      have hh := (probabilityVelocity_iterated_split hF x hr hlam hl huT.1
        (huT.2.trans_lt hT1) hR hρ z (n:=k)).abs_const_mul a
      have hvs : ContDiff ℝ (⊤:ℕ∞) (probabilityVelocity F x r (q u)) :=
        (contDiff_const (c:=(-r:ℝ))).smul (conditionalFieldMean_smooth hF x hr.le hl huT.1 (huT.2.trans_lt hT1))
      rw [←TensorEnergy.multilinearTensor_const_smul a (probabilityVelocity F x r (q u)) hvs z] at hh
      apply hh.mono (mul_nonneg (abs_nonneg _) (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)))
      exact mul_le_of_le_one_left (div_nonneg (normalizedTensorMajorant_nonneg _ _) (pow_nonneg hR.le _)) ha
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hh := hbound d R 1 X V hR hR1 (by norm_num) le_rfl hVX 1 ⟨by norm_num,le_rfl⟩ y
  have he : (fun z => X (1,z))=probabilityTransport hF x hr.le hl hT0 hT1 s t := by
    funext z
    dsimp [X,q,a]
    rw [mul_one,add_sub_cancel]
    exact spatialTransport_eq hF x hr.le hl hT0 hT1 s t z
  rwa [he] at hh
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.TensorEnergy
open scoped Classical BigOperators RealInnerProductSpace

def matrixArray (d : ℕ) : (Point d →L[ℝ] Point d) →L[ℝ] ((Unit ⊕ Unit → Fin d) → ℝ) :=
  ContinuousLinearMap.pi fun c =>
    (innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))).comp
      (ContinuousLinearMap.apply ℝ (Point d) (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))))

lemma matrixArray_apply {d : ℕ} (A : Point d →L[ℝ] Point d) (c : Unit ⊕ Unit → Fin d) :
    matrixArray d A c=inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl ())))
      (A (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ())))) := rfl

def jacobianSlots (n : ℕ) : (Unit ⊕ Unit) ⊕ Fin n ≃ Unit ⊕ Fin (n+1) where
  toFun := Sum.elim (Sum.elim Sum.inl (fun _ => Sum.inr (Fin.last n)))
    (fun i => Sum.inr i.castSucc)
  invFun := Sum.elim (fun u => Sum.inl (Sum.inl u))
    (Fin.lastCases (Sum.inl (Sum.inr ())) Sum.inr)
  left_inv := by rintro ((u|u)|i) <;> simp
  right_inv := by
    rintro (u|i)
    · rfl
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

@[simp] lemma jacobianSlots_symm_out (n : ℕ) :
    (jacobianSlots n).symm (Sum.inl ())=Sum.inl (Sum.inl ()) := rfl
@[simp] lemma jacobianSlots_symm_last (n : ℕ) :
    (jacobianSlots n).symm (Sum.inr (Fin.last n))=Sum.inl (Sum.inr ()) := by simp [jacobianSlots]
@[simp] lemma jacobianSlots_symm_init {n : ℕ} (i : Fin n) :
    (jacobianSlots n).symm (Sum.inr i.castSucc)=Sum.inr i := by simp [jacobianSlots]

lemma arrayTensor_jacobian {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) (c : (Unit ⊕ Unit) ⊕ Fin n → Fin d) :
    arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d (fderiv ℝ f z)) y) c=
      multilinearTensor (iteratedFDeriv ℝ (n+1) f y) (c ∘ (jacobianSlots n).symm) := by
  have hd : ContDiff ℝ (⊤:ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  change arrayTensor (iteratedFDeriv ℝ n ((matrixArray d) ∘ fderiv ℝ f) y) c = _
  rw [(matrixArray d).iteratedFDeriv_comp_left hd.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))]
  simp only [arrayTensor,ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply,matrixArray_apply,multilinearTensor,
    jacobianSlots_symm_out,iteratedFDeriv_succ_apply_right,jacobianSlots_symm_last]
  have hv : (Fin.init fun i => EuclideanSpace.basisFun (Fin d) ℝ (c ((jacobianSlots n).symm (Sum.inr i))))=
      (fun i => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr i))) := by
    funext i
    change EuclideanSpace.basisFun (Fin d) ℝ (c ((jacobianSlots n).symm (Sum.inr i.castSucc)))=_
    rw [jacobianSlots_symm_init]
  rw [hv]

lemma AllSplitBound.jacobian {d n : ℕ} {f : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (y : Point d) {C : ℝ}
    (h : AllSplitBound (multilinearTensor (iteratedFDeriv ℝ (n+1) f y)) C) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n (fun z => matrixArray d (fderiv ℝ f z)) y)) C := by
  have hh := h.reindex (jacobianSlots n).symm
  convert hh using 1
  ext c
  exact arrayTensor_jacobian hf y c
lemma allSplit_jacobian_comp {d n : ℕ} {f g : Point d → Point d}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k)
    (R : ℝ) (hR : 0<R) (y : Point d)
    (ha : ∀k≤n+1,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k g (f y))) (A k/R^(k-1)))
    (hb : ∀k≤n,AllSplitBound (multilinearTensor (iteratedFDeriv ℝ k f y)) (B k/R^(k-1))) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      ((fun z => matrixArray d (fderiv ℝ g z)) ∘ f) y))
      ((∑c : OrderedFinpartition n,A (c.length+1)*∏i,B (c.partSize i))/R^n) := by
  have hj : ContDiff ℝ (⊤:ℕ∞) (fun z => matrixArray d (fderiv ℝ g z)) :=
    (matrixArray d).contDiff.comp (hg.fderiv_right (by simp))
  have hh := array_composition_scale (n:=n) y hf hj (fun k => A (k+1)) B
    (fun _ => hA _) hB R hR 0
    (fun k hk => by
      have h := AllSplitBound.jacobian (n:=k) hg (f y) (ha (k+1) (by omega))
      simpa only [Nat.add_sub_cancel,Nat.add_zero] using h) hb
  simpa only [Nat.add_zero] using hh
end LogConcaveSampling.TensorEnergy

end

end

end

end OAI
