import Mathlib
import OAI.Analysis.Conductivity.Walls.WallSurfaceMomentInverse
import OAI.Analysis.Conductivity.Walls.CriticalWallTensor
import OAI.Analysis.Conductivity.Walls.WallHalfspaceIntegral

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise

def wallHomogeneousTensor (χ v : Box3 → ℝ) (a : (ℝ×ℝ) → ℝ) : Coord3 → Mat3 :=
  wallMatrix (fun p => χ p*a p.1)
    (fun p => χ p*(wallQuotient (wallHomogeneousNumerator (1,0) v a) p/wallQuotient (wallDerivative v) p))

lemma wallHomogeneousTensor_smooth {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallHomogeneousTensor χ v a) :=
  wallMatrix_smooth (hχ.mul (ha.comp contDiff_fst))
    (smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha)
      (wallDerivative_smooth hv) hne)

lemma wallHomogeneousTensor_compact {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ} (hs : HasCompactSupport χ) :
    HasCompactSupport (wallHomogeneousTensor χ v a) ∧
      tsupport (wallHomogeneousTensor χ v a)⊆boxCoordinates ⁻¹' tsupport χ :=
  ⟨wallMatrix_compact hs.mul_right hs.mul_right,
    wallMatrix_tsupport tsupport_mul_subset_left tsupport_mul_subset_left⟩

theorem wallHomogeneousTensor_source_eq {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (x : Coord3) (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) :
    symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 0 x=0 ∧
    symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 1 x=0 := by
  let p := boxCoordinates x
  let A := fun q => χ q*(fun q : Box3 => a q.1) q
  let B := fun q => χ q*(wallQuotient (wallHomogeneousNumerator (1,0) v a) q/wallQuotient (wallDerivative v) q)
  have hA := hχ.mul ((ha.comp contDiff_fst))
  have hB := smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha) (wallDerivative_smooth hv) hne
  have hxe : χ p=1 := hx.eq_of_nhds
  have hp : p∈tsupport χ := subset_tsupport χ (by change χ p≠0; rw [hxe]; norm_num)
  have hqn : ∀ᶠ q in 𝓝 p,wallQuotient (wallDerivative v) q≠0 :=
    (wallQuotient_smooth (wallDerivative_smooth hv)).continuous.continuousAt.eventually_ne (hne p hp)
  have hAe : A =ᶠ[𝓝 p] (fun q : Box3 => a q.1) := hx.mono (fun q hq => by dsimp [A]; rw [hq,one_mul])
  have hFe : (fun q => A q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => (fun q : Box3 => a q.1) q*wallDerivative v q) := hAe.mono (fun q hq => by dsimp only; rw [hq])
  have hGe : (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) =ᶠ[𝓝 p]
      (fun q => (fun q : Box3 => a q.1) q*wallAlong (1,0) v q+wallHomogeneousNumerator (1,0) v a q) := by
    filter_upwards [hx,hqn] with q hq hqn
    dsimp [A,B]
    rw [hq,one_mul,one_mul,wall_ratio_multiply (wallHomogeneousNumerator_smooth (1,0) hv ha)
      (wallDerivative_smooth hv) (wallHomogeneousNumerator_zero (1,0) v a) hz q hqn]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) A at hA
  change ContDiff ℝ (↑(⊤ : ℕ∞)) B at hB
  have hsource := wallMatrix_sources hA hB hv x
  change symmetricSource (wallMatrix A B) (wallCoordinatePair v) 0 x=_ ∧
    symmetricSource (wallMatrix A B) (wallCoordinatePair v) 1 x=_
  rw [hsource.1,hsource.2]
  change wallDerivative A p=0 ∧ _=0
  refine ⟨?_,?_⟩
  · change fderiv ℝ A p (0,1)=0
    rw [hAe.fderiv_eq]
    exact wallDerivative_pullback (ha.differentiable (by simp)) p
  · change fderiv ℝ (fun q => A q*wallDerivative v q) p ((1,0),0)+
      fderiv ℝ (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p (0,1)=0
    rw [hFe.fderiv_eq,hGe.fderiv_eq]
    exact (wall_homogeneous_flux_equations (1,0) hv ha p).2

theorem wallHomogeneousTensor_weak_moments {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0) :
    let H := wallHomogeneousTensor χ v a
    let u := wallCoordinatePair v
    (∀ j,ContDiff ℝ (↑(⊤ : ℕ∞)) (symmetricSource H u j)) ∧
    (∀ j,HasCompactSupport (symmetricSource H u j)) ∧
    (∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=
        -(∫ x,ψ x*symmetricSource H u j x)) ∧
    (∫ x,symmetricSource H u 0 x)=0 ∧ (∫ x,symmetricSource H u 1 x)=0 ∧
    (∫ x,u x 1*symmetricSource H u 0 x-u x 0*symmetricSource H u 1 x)=0 :=
  symmetric_cutoff_sources _ (wallHomogeneousTensor_smooth hχ hv ha hne)
    (wallHomogeneousTensor_compact hs).1 (wallMatrix_symmetric _ _) _ (wallCoordinatePair_smooth hv)

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

theorem wallHomogeneousTensor_transfers {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hs : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (hcut : ∀ q,χ (q,0)*a q=a q) :
    let H := wallHomogeneousTensor χ v a
    let u := wallCoordinatePair v
    let r := fun (j : Fin 2) (p : Box3) => symmetricSource H u j (boxCoordinates.symm p)
    let U := (Set.univ : Set (ℝ×ℝ)) ×ˢ Ioi (0:ℝ)
    (∫ p in U,r 0 p)= -(∫ q : ℝ×ℝ,a q) ∧
    (∫ p in U,r 1 p)= -(∫ q : ℝ×ℝ,a q*wallAlong (1,0) v (q,0)) ∧
    (∫ p in U,v p*r 0 p-p.1.1*r 1 p)=
      -(∫ q : ℝ×ℝ,a q*(v (q,0)-q.1*wallAlong (1,0) v (q,0))) := by
  dsimp only
  let A := fun p => χ p*a p.1
  let B := fun p => χ p*(wallQuotient (wallHomogeneousNumerator (1,0) v a) p/wallQuotient (wallDerivative v) p)
  have hA := hχ.mul (ha.comp contDiff_fst)
  have hB := smooth_wall_cutoff_ratio hχ (wallHomogeneousNumerator_smooth (1,0) hv ha) (wallDerivative_smooth hv) hne
  change ContDiff ℝ (↑(⊤ : ℕ∞)) A at hA
  change ContDiff ℝ (↑(⊤ : ℕ∞)) B at hB
  have he₀ (p : Box3) : symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 0
        (boxCoordinates.symm p)=wallDerivative A p := by
    simpa only [boxCoordinates.apply_symm_apply,wallHomogeneousTensor,A,B] using (wallMatrix_sources hA hB hv (boxCoordinates.symm p)).1
  have he₁ (p : Box3) : symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) 1
        (boxCoordinates.symm p)=wallAlong (1,0) (fun q => A q*wallDerivative v q) p+
      wallDerivative (fun q => A q*wallAlong (1,0) v q+B q*wallDerivative v q) p := by
    simpa only [boxCoordinates.apply_symm_apply,wallHomogeneousTensor,A,B] using (wallMatrix_sources hA hB hv (boxCoordinates.symm p)).2
  simp_rw [he₀,he₁]
  have hh := wall_matrix_halfspace_moments hA hB hs.mul_right hs.mul_right hv hz
  simpa only [A,hcut] using hh

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

def wallActualMoment (v : Box3 → ℝ) (q : ℝ×ℝ) : Fin 3 → ℝ :=
  ![1,wallAlong (1,0) v (q,0),v (q,0)-q.1*wallAlong (1,0) v (q,0)]

lemma wallActualMoment_limit {v : Box3 → ℝ} {σ lam : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (he : ∀ q : ℝ×ℝ,v (q,0)=σ*Real.exp (-lam*q.1)) (q : ℝ×ℝ) :
    wallActualMoment v q=wallMomentBasis σ lam q.1 := by
  have hs : wallAlong (1,0) v (q,0)= -σ*lam*Real.exp (-lam*q.1) := by
    have hpath : HasDerivAt (fun s : ℝ => ((s,q.2),(0:ℝ))) ((1,0),0) q.1 :=
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)).prodMk (hasDerivAt_const q.1 0)
    have hd := ((hv.differentiable (by simp) (q,0)).hasFDerivAt.comp_hasDerivAt q.1 hpath)
    have hd' : HasDerivAt (fun s : ℝ => σ*Real.exp (-lam*s))
        (-σ*lam*Real.exp (-lam*q.1)) q.1 := by
      convert! (((hasDerivAt_id q.1).const_mul (-lam)).exp.const_mul σ) using 1
      first | rfl | (simp only [id_eq]; ring)
    have heq : (fun s : ℝ => v ((s,q.2),0))=(fun s => σ*Real.exp (-lam*s)) := funext (fun s => he (s,q.2))
    change HasDerivAt (fun s : ℝ => v ((s,q.2),0)) (wallAlong (1,0) v (q,0)) q.1 at hd
    rw [heq] at hd
    exact hd.unique hd'
  ext i
  fin_cases i
  · rfl
  · exact hs
  · change v (q,0)-q.1*wallAlong (1,0) v (q,0)=σ*(1+lam*q.1)*Real.exp (-lam*q.1)
    rw [he,hs]
    ring

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P] [LocallyCompactSpace P]

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
lemma wallActualMoment_joint_continuous {v : P → Box3 → ℝ}
    (hv : Continuous (fun pq : P × Box3 => v pq.1 pq.2))
    (hvs : Continuous (fun pq : P × Box3 => wallAlong (1,0) (v pq.1) pq.2)) (i : Fin 3) :
    Continuous (fun pq : P × (ℝ×ℝ) => wallActualMoment (v pq.1) pq.2 i) := by
  have hmap : Continuous (fun pq : P × (ℝ×ℝ) => (pq.1,(pq.2,(0:ℝ)))) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  fin_cases i
  · exact continuous_const
  · exact hvs.comp hmap
  · exact (hv.comp hmap).sub (continuous_snd.fst.mul (hvs.comp hmap))

theorem actual_wall_moment_uniform_inverse {l r a b σ lam : ℝ}
    (hlr : l<r) (hab : a<b) (hσ : σ≠0) (hlam : lam≠0)
    {v : P → Box3 → ℝ} {p₀ : P}
    (hv₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (v p₀))
    (hv : Continuous (fun pq : P × Box3 => v pq.1 pq.2))
    (hvs : Continuous (fun pq : P × Box3 => wallAlong (1,0) (v pq.1) pq.2))
    (hlim : ∀ q : ℝ×ℝ,v p₀ (q,0)=σ*Real.exp (-lam*q.1)) :
    ∃ χ η : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
      HasCompactSupport χ ∧ HasCompactSupport η ∧
      tsupport χ⊆Icc l r ∧ tsupport η⊆Ioo a b ∧
      ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,∀ m : Fin 3 → ℝ,
        ∃ c : Fin 3 → ℝ,(∀ i,‖c i‖≤C*‖m‖) ∧
          let f := fun q : ℝ×ℝ => (χ q.1*(c ⬝ᵥ wallMomentBasis σ lam q.1))*η q.2
          ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
          tsupport f⊆Icc l r ×ˢ Ioo a b ∧
          (∀ i,(∫ q,f q*wallActualMoment (v p) q i)=m i) := by
  exact wall_surface_moment_uniform_inverse hlr hab hσ hlam
    (wallActualMoment_joint_continuous hv hvs) (wallActualMoment_limit hv₀ hlim)

end ScalarConductivity

end

end OAI
