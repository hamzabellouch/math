import Mathlib
import OAI.Analysis.Commutator.Average
import OAI.Analysis.Commutator.CompactAverage
import OAI.Analysis.Commutator.UnitaryHaar
import OAI.Analysis.Commutator.WeakConvergence

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

open MeasureTheory Filter

namespace Kadison.RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))

def unitaryRepresentation : unitary A →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    { toFun := fun u => ⟨ρ (u:A),Unitary.map_mem ρ u.property⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' u v := Subtype.ext (map_mul ρ (u:A) (v:A)) }

lemma conjugate_distance (Y : K →L[ℂ] K) (u : unitary A) :
    ‖CompactAverage.conjugate (unitaryRepresentation ρ) Y u-Y‖=‖Y*ρ (u:A)-ρ (u:A)*Y‖ := by
  let w : unitary (K →L[ℂ] K) := ⟨ρ (u:A),Unitary.map_mem ρ u.property⟩
  have he : CompactAverage.conjugate (unitaryRepresentation ρ) Y u-Y=
      ((w:K →L[ℂ] K)*Y-Y*(w:K →L[ℂ] K))*star (w:K →L[ℂ] K) := by
    change (w:K →L[ℂ] K)*Y*star (w:K →L[ℂ] K)-Y=_
    rw [sub_mul,mul_assoc Y (w:K →L[ℂ] K) (star (w:K →L[ℂ] K)),w.property.2,mul_one]
  rw [he,CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem w.property),norm_sub_rev]

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]

variable (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def stageUnitaryMap (n : ℕ) : unitary (Matrix (I n) (I n) ℂ) →* unitary A where
  toFun u := ⟨φ n (u : Matrix (I n) (I n) ℂ),Unitary.map_mem (φ n) u.property⟩
  map_one' := Subtype.ext (map_one (φ n))
  map_mul' u v := Subtype.ext (map_mul (φ n) (u:Matrix (I n) (I n) ℂ) (v:Matrix (I n) (I n) ℂ))

def stageUnitaryRepresentation (n : ℕ) : unitary (Matrix (I n) (I n) ℂ) →* (K ≃ₗᵢ[ℂ] K) :=
  (unitaryRepresentation ρ).comp (stageUnitaryMap I φ n)

omit [∀ (n : ℕ), Nonempty (I n)] in
lemma stageUnitary_continuous (n : ℕ) (x : K) :
    Continuous fun u => stageUnitaryRepresentation ρ I φ n u x := by
  change Continuous fun u : unitary (Matrix (I n) (I n) ℂ) => ρ (φ n (u:_)) x
  exact (((ρ.comp (φ n)).toLinearMap.continuous_of_finiteDimensional).comp
    continuous_subtype_val).clm_apply continuous_const

lemma exists_stage_average (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) (n : ℕ) :
    ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      ∀ a,Z*ρ (φ n a)=ρ (φ n a)*Z := by
  classical
  let := UnitaryHaar.compactUnitary (Matrix (I n) (I n) ℂ)
  let : MeasurableSpace (unitary (Matrix (I n) (I n) ℂ)) := borel _
  let : BorelSpace (unitary (Matrix (I n) (I n) ℂ)) := ⟨rfl⟩
  let U := stageUnitaryRepresentation ρ I φ n
  let μ := UnitaryHaar.probability (unitary (Matrix (I n) (I n) ℂ))
  obtain ⟨Z,hZ,hcomm,hcoeff⟩ := CompactAverage.exists_average U (stageUnitary_continuous ρ I φ n) Y μ
  refine ⟨Z,hZ,?_,?_⟩
  · apply WeakOperatorIntegral.difference_norm μ (CompactAverage.conjugate U Y) _ Z hcoeff Y hδ
    · intro u
      exact (conjugate_distance ρ Y (stageUnitaryMap I φ n u)).le.trans (hb _)
    · intro x y
      exact ((CompactAverage.conjugate_continuous U (stageUnitary_continuous ρ I φ n) Y x).inner
        continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · let D : Matrix (I n) (I n) ℂ →ₗ[ℂ] (K →L[ℂ] K) :=
      { toFun := fun a => Z*ρ (φ n a)-ρ (φ n a)*Z
        map_add' := by intro a b; simp only [map_add,mul_add,add_mul]; abel
        map_smul' := by intro z a; simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub]; rfl }
    have hD : D=0 := by
      apply LinearMap.ext_on (CStarAlgebra.span_unitary (Matrix (I n) (I n) ℂ))
      intro u hu
      exact sub_eq_zero.mpr (hcomm ⟨u,hu⟩)
    intro a
    exact sub_eq_zero.mp (congrArg (fun D : Matrix (I n) (I n) ℂ →ₗ[ℂ] (K →L[ℂ] K) => D a) hD)

theorem exists_tower_average (hφ : Monotone (fun n => (φ n).range))
    (Y : K →L[ℂ] K) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀ u : unitary A,‖Y*ρ (u:A)-ρ (u:A)*Y‖≤δ) :
    ∃ Z : K →L[ℂ] K,‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      ∀ a : K →L[ℂ] K,a∈Set.centralizer (Set.centralizer
        ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K))) → Z*a=a*Z := by
  choose T hn hd hc using exists_stage_average ρ I φ Y hδ hb
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨Z,hZ,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T ‖Y‖ (norm_nonneg Y) hn
  have hconv : WeakOperatorLimit.Converges T Z (ω:Filter ℕ) := hlim
  refine ⟨Z,hZ,hconv.dist Y hδ (Eventually.of_forall hd),?_⟩
  have hstage (n : ℕ) (a : Matrix (I n) (I n) ℂ) : Z*ρ (φ n a)=ρ (φ n a)*Z := by
    apply hconv.commutes
    apply (Ultrafilter.of_le atTop)
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨b,hb⟩ := hφ hm (show φ n a∈(φ n).range from ⟨a,rfl⟩)
    rw [←hb]
    exact hc m b
  have hcent : Z∈Set.centralizer ((iSup fun n => (ρ.comp (φ n)).range : StarSubalgebra ℂ (K →L[ℂ] K)) : Set (K →L[ℂ] K)) := by
    have hcomm : (iSup fun n => (ρ.comp (φ n)).range)≤StarSubalgebra.centralizer ℂ ({Z} : Set (K →L[ℂ] K)) := by
      apply iSup_le
      intro n
      rintro a ⟨b,rfl⟩
      rw [StarSubalgebra.mem_centralizer_iff]
      intro z hz
      have he : z=Z := Set.mem_singleton_iff.mp hz
      subst z
      constructor
      · exact hstage n b
      · have hh := congrArg star (hstage n (star b))
        simpa only [star_mul,←map_star,star_star] using! hh.symm
    intro a ha
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp (hcomm ha)) Z (Set.mem_singleton Z)).1.symm
  intro a ha
  exact ha Z hcent

end Kadison.RepresentedTower

end

end
end

end OAI
