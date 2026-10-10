import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Value
import OAI.Analysis.MatrixSigning.Potential.Pack

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

lemma unpack_kkt (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d)
    (hz : kktSystem ε S η z = 0) :
    realTrace (mCoord d z) + realTrace (nCoord d z) = 1 ∧
    residual S η (unpack z) = 0 ∧
    sandwich (invH (xCoord d z)) (mCoord d z) = η (nCoord d z) + ε • (Hermitian.one : H d) ∧
    sandwich (invH (yCoord d z)) (nCoord d z) = η (mCoord d z) + ε • (Hermitian.one : H d) := by
  have htr := congrArg Prod.fst hz
  have ht := congrArg (fun v : Vars d => pairEquiv d v.2.1) hz
  have hs := congrArg (fun v : Vars d => pairEquiv d v.2.2) hz
  have ht₁ := congrArg Prod.fst ht
  have ht₂ := congrArg Prod.snd ht
  have hs₁ := congrArg Prod.fst hs
  have hs₂ := congrArg Prod.snd hs
  change inner ℝ (Hermitian.one : H d) (mCoord d z) +
    inner ℝ (Hermitian.one : H d) (nCoord d z) - 1 = 0 at htr
  rw [inner_one,inner_one] at htr
  refine ⟨sub_eq_zero.mp htr,?_,?_,?_⟩
  · change tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z) = 0 at ht₁
    change tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z) = 0 at ht₂
    apply Prod.ext
    · change invH (xCoord d z) + S + η (yCoord d z) - tCoord d z • (Hermitian.one : H d) = 0
      calc
        _ = -(tCoord d z • (Hermitian.one : H d) - invH (xCoord d z) - S - η (yCoord d z)) := by module
        _ = 0 := by rw [ht₁,neg_zero]
    · change invH (yCoord d z) - S + η (xCoord d z) - tCoord d z • (Hermitian.one : H d) = 0
      calc
        _ = -(tCoord d z • (Hermitian.one : H d) - invH (yCoord d z) + S - η (xCoord d z)) := by module
        _ = 0 := by rw [ht₂,neg_zero]
  · change sandwich (invH (xCoord d z)) (mCoord d z) - η (nCoord d z) - ε • (Hermitian.one : H d) = 0 at hs₁
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hs₁)
  · change sandwich (invH (yCoord d z)) (nCoord d z) - η (mCoord d z) - ε • (Hermitian.one : H d) = 0 at hs₂
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hs₂)

lemma value_eq_of_system (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (hη : SymmetricMap η) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ psdCone d) (hQ : nCoord d z ∈ psdCone d)
    (hz : kktSystem ε S η z = 0) : value ε S η = objective ε (unpack z) := by
  obtain ⟨htr,ht,hx,hy⟩ := unpack_kkt ε S η z hz
  exact value_eq_of_kkt ε S η hη (unpack z) ⟨hX,hY⟩ (mCoord d z) (nCoord d z)
    hP hQ htr hx hy ht

lemma contDiff_objective (ε : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (objective (d := d) ε) := by
  have ht : ContDiff ℝ n (fun z : Point d => inner ℝ (Hermitian.one : H d) (z.2.1+z.2.2)) :=
    (innerSL ℝ (Hermitian.one : H d)).contDiff.comp (contDiff_snd.fst.add contDiff_snd.snd)
  have hh := contDiff_fst.add ((contDiff_const (c := ε)).mul ht)
  simp only [inner_one] at hh
  exact hh

lemma contDiff_unpack {n : WithTop ℕ∞} : ContDiff ℝ n (unpack (d := d)) :=
  (tCoord d).contDiff.prodMk ((xCoord d).contDiff.prodMk (yCoord d).contDiff)

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

theorem contDiffAt_value [NeZero d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (S : E → H d) (η : E → (H d →L[ℝ] H d)) (b : E)
    (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηpos : ∀ A ∈ psdCone d, η b A ∈ psdCone d)
    (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S b) (hS₂ : S b ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S b) (η b))
    (hmin : ∀ w ∈ feasible (S b) (η b), objective ε z ≤ objective ε w) :
    ContDiffAt ℝ ∞ (fun a => value ε (S a) (η a)) b := by
  have hsym := hηsym.self_of_nhds
  obtain ⟨P,Q,hP,hQ,_,_,htr,hPX,hQY,ht,hx,hy⟩ :=
    kkt (S b) (η b) hηpos hsym hε hS₁ hS₂ z hz hmin
  obtain ⟨J,hJ⟩ := kkt_regular z.2.1 z.2.2 P Q (η b) hηpos hsym hz.1.1 hz.1.2 hP hQ hε hPX hQY
  have he := pack_kkt ε (S b) (η b) z P Q htr ht hx hy
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_kkt_branch ε (S b,η b) (pack z P Q) hz.1.1 hz.1.2 J hJ
  let g : E → Vars d := fun a => f (S a,η a)
  have hg : g b = pack z P Q := hf
  have hgc : ContDiffAt ℝ ∞ g b := hfc.comp b (hS.prodMk hη)
  have hge : ∀ᶠ a in 𝓝 b, kktSystem ε (S a) (η a) (g a) = 0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with a ha
    exact ha.trans he
  have hXg : ∀ᶠ a in 𝓝 b, xCoord d (g a) ∈ pd d := by
    apply ((xCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change xCoord d (g b) ∈ pd d
    rw [hg]
    exact hz.1.1
  have hYg : ∀ᶠ a in 𝓝 b, yCoord d (g a) ∈ pd d := by
    apply ((yCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change yCoord d (g b) ∈ pd d
    rw [hg]
    exact hz.1.2
  have hPg : ∀ᶠ a in 𝓝 b, mCoord d (g a) ∈ pd d := by
    apply ((mCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change mCoord d (g b) ∈ pd d
    rw [hg]
    exact hP
  have hQg : ∀ᶠ a in 𝓝 b, nCoord d (g a) ∈ pd d := by
    apply ((nCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change nCoord d (g b) ∈ pd d
    rw [hg]
    exact hQ
  have hval : (fun a => value ε (S a) (η a)) =ᶠ[𝓝 b] (fun a => objective ε (unpack (g a))) := by
    filter_upwards [hηsym,hge,hXg,hYg,hPg,hQg] with a ha he hx hy hp hq
    exact value_eq_of_system ε (S a) (η a) ha (g a) hx hy hp.posSemidef hq.posSemidef he
  exact ((contDiff_objective ε).contDiffAt.comp b
    ((contDiff_unpack (d := d)).contDiffAt.comp b hgc)).congr_of_eventuallyEq hval

end
end CurrentKS.Variational

end OAI
