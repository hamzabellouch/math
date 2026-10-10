import Mathlib.Analysis.Normed.Module.FiniteDimension
import OAI.Analysis.FactorGeneration.ProjectionComparison
import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

def blockStarAlgebra (N : VonNeumannAlgebra H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {a | a ∈ N ∧ ∀ i, (Q.piece i).val.val*a=a*(Q.piece i).val.val}
  zero_mem' := ⟨N.zero_mem,by simp⟩
  one_mem' := ⟨N.one_mem,by simp⟩
  add_mem' ha hb := ⟨N.add_mem ha.1 hb.1,by
    intro i
    simp only [mul_add,add_mul,ha.2 i,hb.2 i]⟩
  mul_mem' ha hb := ⟨N.mul_mem ha.1 hb.1,by
    intro i
    rw [← mul_assoc,ha.2 i,mul_assoc,hb.2 i,← mul_assoc]⟩
  algebraMap_mem' c := ⟨N.toStarSubalgebra.algebraMap_mem c,by
    intro i
    exact (Algebra.commutes c _).symm⟩
  star_mem' ha := ⟨star_mem ha.1,by
    intro i
    have hs : star (Q.piece i).val.val=(Q.piece i).val.val :=
      congrArg Subtype.val (Q.piece i).property.isSelfAdjoint.star_eq
    simpa only [star_mul,hs] using (congrArg star (ha.2 i)).symm⟩

theorem blockStarAlgebra_bicommutant (N : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (Q.blockStarAlgebra N : Set (H →L[ℂ] H))) =
      (Q.blockStarAlgebra N : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    refine ⟨?_,?_⟩
    · change a ∈ (N : Set (H →L[ℂ] H))
      rw [← N.centralizer_centralizer]
      intro b hb
      exact ha b (fun c hc => hb c hc.1)
    · intro i
      apply ha
      intro b hb
      exact (hb.2 i).symm
  · intro a ha b hb
    exact (hb a ha).symm

def blockVonNeumann (N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := Q.blockStarAlgebra N
  centralizer_centralizer' := Q.blockStarAlgebra_bicommutant N

theorem blockVonNeumann_le (N : VonNeumannAlgebra H) : Q.blockVonNeumann N ≤ N :=
  fun _ h => h.1

theorem blockVonNeumann_mem_iff (N : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    a.val ∈ Q.blockVonNeumann N ↔ a.val ∈ N ∧ ∀ i, Commute (Q.piece i).val a := by
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨ha,fun i => Subtype.ext (hc i)⟩
  · rintro ⟨ha,hc⟩
    exact ⟨ha,fun i => congrArg Subtype.val (hc i).eq⟩

theorem piece_commute (i j : Fin Q.size) : Commute (Q.piece i).val (Q.piece j).val := by
  by_cases h : i=j
  · subst j; exact Commute.refl _
  · show (Q.piece i).val*(Q.piece j).val=(Q.piece j).val*(Q.piece i).val
    rw [Q.orthogonal i j h,Q.orthogonal j i (Ne.symm h)]

theorem piece_mem_blockVonNeumann (N : VonNeumannAlgebra H)
    (hN : ∀ i, (Q.piece i).val.val ∈ N) (i : Fin Q.size) :
    (Q.piece i).val.val ∈ Q.blockVonNeumann N :=
  (Q.blockVonNeumann_mem_iff N _).mpr ⟨hN i,fun j => Q.piece_commute j i⟩

theorem compression_mem_blockVonNeumann (N : VonNeumannAlgebra H)
    (hN : ∀ i, (Q.piece i).val.val ∈ N) (i : Fin Q.size)
    (a : M.toStarSubalgebra) (ha : a.val ∈ N) :
    ((Q.piece i).val*a*(Q.piece i).val).val ∈ Q.blockVonNeumann N := by
  apply (Q.blockVonNeumann_mem_iff N _).mpr
  refine ⟨N.mul_mem (N.mul_mem (hN i) ha) (hN i),?_⟩
  intro j
  by_cases h : j=i
  · subst j
    show (Q.piece i).val*((Q.piece i).val*a*(Q.piece i).val)=
      ((Q.piece i).val*a*(Q.piece i).val)*(Q.piece i).val
    simp only [← mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
    simp only [mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
  · show (Q.piece j).val*((Q.piece i).val*a*(Q.piece i).val)=
      ((Q.piece i).val*a*(Q.piece i).val)*(Q.piece j).val
    rw [← mul_assoc,← mul_assoc,Q.orthogonal j i h,zero_mul,zero_mul]
    simp only [mul_assoc,Q.orthogonal i j (Ne.symm h),mul_zero]

end CornerPartition

end

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hirr in
/-- A self-adjoint element of the relative corner commutant is scalar in
that corner, including the zero corner. -/
theorem selfAdjoint_corner_commutant_scalar (p : AlgebraProjection M)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hcL : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,hfix,hQ,hd⟩ :=
      exists_finite_spectral_approximation_preserving_commutant p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      have htriv := corner_commutant_projection_trivial τ P hirr p (Q.piece i)
        (Q.piece_le i) (fun a => hQ (p.val*(a : M.toStarSubalgebra)*p.val)
          (hcomm a) (by
            show p.val*(p.val*(a : M.toStarSubalgebra)*p.val)=
              (p.val*(a : M.toStarSubalgebra)*p.val)*p.val
            simp only [← mul_assoc,p.property.isIdempotentElem.eq]
            simp only [mul_assoc,p.property.isIdempotentElem.eq]) i)
      rcases htriv with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i, (d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  have hm : c ∈ L := by
    change c ∈ (L : Set M.toStarSubalgebra)
    rw [← hclosed.closure_eq]
    exact hcL
  exact Submodule.mem_span_singleton.mp hm |>.imp (fun z hz => hz.symm)

omit [CompleteSpace P] in
/-- Taking adjoints preserves the supported relative-commutant condition. -/
theorem corner_commutant_star (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∀ a : P, Commute (star c) (p.val*(a : M.toStarSubalgebra)*p.val) := by
  intro a
  have h := congrArg star (hcomm (star a)).eq
  change star (c*(p.val*star (a : M.toStarSubalgebra)*p.val)) =
    star ((p.val*star (a : M.toStarSubalgebra)*p.val)*c) at h
  show star c*(p.val*(a : M.toStarSubalgebra)*p.val)=
    (p.val*(a : M.toStarSubalgebra)*p.val)*star c
  simpa only [star_mul,star_star,p.property.isSelfAdjoint.star_eq,
    mul_assoc] using h.symm

include τ hirr in
/-- Exact irreducibility in pMp, stated in ambient coordinates. The scalar
is the normalized corner trace when p is nonzero. -/
theorem corner_commutant_scalar (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  have hstar := corner_commutant_star P p c hcomm
  have hreal : ∀ a : P, Commute (ℜ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left (2 : ℝ)⁻¹
  have himag : ∀ a : P, Commute (ℑ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left (2 : ℝ)⁻¹).smul_left (-Complex.I)
  obtain ⟨a,ha⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr]) hreal
  obtain ⟨b,hb⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr]) himag
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection M))

theorem pinch_eq_self_of_commutes (c : M.toStarSubalgebra)
    (hc : ∀ i, Commute (Q.piece i).val c) : Q.pinch c=c := by
  unfold pinch
  calc (∑ i, (Q.piece i).val*c*(Q.piece i).val) = ∑ i, c*(Q.piece i).val := by
         apply Finset.sum_congr rfl
         intro i _
         rw [(hc i).eq,mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
       _ = c := by rw [← Finset.mul_sum,Q.total]; exact mul_one c

include τ in
theorem block_commutant_scalar_blocks
    (hN : ∀ i, (Q.piece i).val.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : insideAlgebra (M := M) (P := Q.blockVonNeumann N),
      (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) :
    ∃ z : Fin Q.size → ℂ, c=∑ i,z i • (Q.piece i).val := by
  have hqi (i : Fin Q.size) : Commute (Q.piece i).val c :=
    hc ⟨(Q.piece i).val,Q.piece_mem_blockVonNeumann N hN i⟩
  have hlocal (i : Fin Q.size) : ∃ z : ℂ,
      (Q.piece i).val*c*(Q.piece i).val=z • (Q.piece i).val := by
    apply corner_commutant_scalar τ (insideAlgebra (M := M) (P := N)) hirr (Q.piece i)
    · simp only [← mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
    · simp only [mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
    · intro a
      have hb : Commute ((Q.piece i).val*(a : M.toStarSubalgebra)*(Q.piece i).val) c :=
        hc ⟨_,Q.compression_mem_blockVonNeumann N hN i a.val a.property⟩
      have hp : Commute ((Q.piece i).val*(a : M.toStarSubalgebra)*(Q.piece i).val)
          (Q.piece i).val := by
        show ((Q.piece i).val*(a : M.toStarSubalgebra)*(Q.piece i).val)*(Q.piece i).val=
          (Q.piece i).val*((Q.piece i).val*(a : M.toStarSubalgebra)*(Q.piece i).val)
        simp only [mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
        simp only [← mul_assoc,(Q.piece i).property.isIdempotentElem.eq]
      exact ((hp.mul_right hb).mul_right hp).symm
  choose z hz using hlocal
  exact ⟨z,(Q.pinch_eq_self_of_commutes c hqi).symm.trans
    (Finset.sum_congr rfl (fun i _ => hz i))⟩

include τ in
theorem block_commutant_mem_subalgebra
    (hN : ∀ i, (Q.piece i).val.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : insideAlgebra (M := M) (P := Q.blockVonNeumann N),
      (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) : c.val ∈ N := by
  obtain ⟨z,rfl⟩ := Q.block_commutant_scalar_blocks τ hN hirr c hc
  change (∑ i,z i • (Q.piece i).val) ∈ insideAlgebra (M := M) (P := N)
  exact (insideAlgebra (M := M) (P := N)).sum_mem
    (fun i _ => (insideAlgebra (M := M) (P := N)).smul_mem (hN i) (z i))

end CornerPartition

end

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def TraceOrthogonal (P : StarSubalgebra ℂ M.toStarSubalgebra) (x : M.toStarSubalgebra) : Prop :=
  ∀ a : P, τ.trace ((a : M.toStarSubalgebra)*x)=0

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
variable (hx : TraceOrthogonal τ P x)
include hx

theorem trace_zero : τ.trace x=0 := by simpa using hx (1 : P)

theorem compression (p : AlgebraProjection M) (hp : p.val ∈ P) :
    TraceOrthogonal τ P (p.val*x*p.val) := by
  intro a
  have h := hx ⟨p.val*(a : M.toStarSubalgebra)*p.val,P.mul_mem (P.mul_mem hp a.property) hp⟩
  change τ.trace ((p.val*(a : M.toStarSubalgebra)*p.val)*x)=0 at h
  calc τ.trace ((a : M.toStarSubalgebra)*(p.val*x*p.val)) =
      τ.trace (p.val*((a : M.toStarSubalgebra)*(p.val*x))) := by
        rw [← mul_assoc (a : M.toStarSubalgebra),τ.trace_mul_comm]
    _ = 0 := by simpa only [mul_assoc] using h

theorem conjugate (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra) ∈ P) :
    TraceOrthogonal τ P (conjugateLinear u x) := by
  intro a
  have h := hx ⟨star (u : M.toStarSubalgebra)*(a : M.toStarSubalgebra)*(u : M.toStarSubalgebra),
    P.mul_mem (P.mul_mem (P.star_mem' hu) a.property) hu⟩
  change τ.trace ((a : M.toStarSubalgebra)*((u : M.toStarSubalgebra)*x*star (u : M.toStarSubalgebra)))=0
  rw [← mul_assoc (a : M.toStarSubalgebra),τ.trace_mul_comm]
  simpa only [mul_assoc] using h

theorem pinch {p : AlgebraProjection M} (Q : CornerPartition p)
    (hQ : ∀ i,(Q.piece i).val ∈ P) : TraceOrthogonal τ P (Q.pinch x) := by
  intro a
  change coordinateTraceLinear τ ((a : M.toStarSubalgebra)*∑ i,(Q.piece i).val*x*(Q.piece i).val)=0
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_eq_zero (fun i _ => hx.compression τ (Q.piece i) (hQ i) a)

theorem cornerScalar_zero (p : AlgebraProjection M) (hp : p.val ∈ P) :
    cornerScalar τ p x=0 := by
  rw [cornerScalar,(hx.compression τ p hp).trace_zero τ,zero_div]

theorem scalarEnergy_zero {p : AlgebraProjection M} (Q : CornerPartition p)
    (hQ : ∀ i,(Q.piece i).val ∈ P) : Q.scalarEnergy τ x=0 := by
  unfold CornerPartition.scalarEnergy
  simp only [hx.cornerScalar_zero τ _ (hQ _),norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,
    Finset.sum_const_zero]

end TraceOrthogonal

/-- If an orthogonal operator is averaged by subalgebra unitaries and all
fixed points lie in the subalgebra, the actual least-norm orbit point is zero. -/
theorem zero_mem_orbitHull_of_orthogonal
    (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (G : Subgroup (unitary M.toStarSubalgebra))
    (hG : ∀ u : G,(u.val : M.toStarSubalgebra) ∈ P)
    (hfixed : ∀ c : M.toStarSubalgebra,
      (∀ u : G,conjugateLinear u.val c=c) → c ∈ P)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ P x) :
    (0 : H) ∈ traceOrbitHull τ G x := by
  obtain ⟨c,_,hc,_,hfix⟩ := traceOrbitHull_minimum τ G x
  have hcP := hfixed c hfix
  have htest : ∀ u : G,τ.trace (star c*conjugateLinear u.val x)=0 :=
    fun u => (hx.conjugate τ u.val (hG u)) ⟨star c,P.star_mem' hcP⟩
  have hz := orbitHull_trace_test_zero τ G x c htest hc
  have hv : baseVector τ c=0 := inner_self_eq_zero.mp hz
  exact hv ▸ hc

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem scalarEnergy_le_energy (x : M.toStarSubalgebra) :
    Q.scalarEnergy τ x ≤ τ.norm₂ (Q.pinch x)^2 := by
  have h := Q.scalarEnergy_le_refineBlocks τ (fun i => single (Q.piece i)) x
  rw [Q.refineBlocks_pinch] at h
  have he : (∑ i,(single (Q.piece i)).pinch x)=Q.pinch x := by
    simp only [single_pinch]
    rfl
  rw [he] at h
  exact h

theorem cornerScalar_eq_of_orthogonal_difference
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hp : p.val ∈ P)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    cornerScalar τ p x=cornerScalar τ p y := by
  have h := (hxy.compression τ p hp).trace_zero τ
  rw [mul_sub,sub_mul,trace_sub,sub_eq_zero] at h
  exact congrArg (fun t : ℂ => t/τ.trace p.val) h

theorem scalarEnergy_eq_of_orthogonal_difference
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hQ : ∀ i,(Q.piece i).val ∈ P)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    Q.scalarEnergy τ x=Q.scalarEnergy τ y := by
  unfold scalarEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [cornerScalar_eq_of_orthogonal_difference τ (p := Q.piece i) P (hQ i) x y hxy]

/-- All later scalar terms are bounded by the already controlled coarse
energy of the subalgebra component. There is no claim that global centering
provides this bound. -/
theorem refinement_scalarEnergy_le_component
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (R : CornerPartition p)
    (hR : ∀ i,(R.piece i).val ∈ P) (hQR : Q.Refines R)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    R.scalarEnergy τ x ≤ τ.norm₂ (Q.pinch y)^2 := by
  rw [R.scalarEnergy_eq_of_orthogonal_difference τ P hR x y hxy]
  have h := Q.refinement_energy_le τ R hQR y
  rw [← Q.pinch_energy τ,← R.pinch_energy τ] at h
  exact (R.scalarEnergy_le_energy τ y).trans h

theorem pinch_mem (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (hQ : ∀ i,(Q.piece i).val ∈ P) (y : M.toStarSubalgebra) (hy : y ∈ P) :
    Q.pinch y ∈ P :=
  P.sum_mem (fun i _ => P.mul_mem (P.mul_mem (hQ i) hy) (hQ i))

/-- Pythagoras separates the orthogonal component from the component in P. -/
theorem orthogonal_component_energy
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hQ : ∀ i,(Q.piece i).val ∈ P)
    (x y : M.toStarSubalgebra) (hy : y ∈ P) (hxy : TraceOrthogonal τ P (x-y)) :
    τ.norm₂ (Q.pinch x)^2 = τ.norm₂ (Q.pinch (x-y))^2+τ.norm₂ (Q.pinch y)^2 := by
  have ho : inner ℂ (baseVector τ (Q.pinch y)) (baseVector τ (Q.pinch (x-y)))=0 := by
    rw [baseVector_inner_eq_trace]
    exact (hxy.pinch τ Q hQ) ⟨star (Q.pinch y),P.star_mem' (Q.pinch_mem P hQ y hy)⟩
  have he : Q.pinch x=Q.pinch y+Q.pinch (x-y) := by rw [Q.pinch_sub]; abel
  rw [he]
  change ‖baseVector τ (Q.pinch y+Q.pinch (x-y))‖^2 = _
  rw [map_add,norm_add_sq (𝕜 := ℂ),ho]
  change τ.norm₂ (Q.pinch y)^2+2*0+τ.norm₂ (Q.pinch (x-y))^2=_
  ring

end CornerPartition

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c) : ∃ z : ℂ,c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hm : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,_,hd⟩ := exists_finite_spectral_approximation p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      rcases hmin (Q.piece i) (Q.piece_le i) with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i,(d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  rw [hclosed.closure_eq] at hm
  exact (Submodule.mem_span_singleton.mp hm).imp (fun z hz => hz.symm)

theorem corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hl : p.val*c=c) (hr : c*p.val=c) :
    ∃ z : ℂ,c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  obtain ⟨a,ha⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr])
  obtain ⟨b,hb⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr])
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_diffuse (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (p : P.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  classical
  by_contra hn
  let pP : AlgebraProjection P := ⟨p,hp⟩
  have hmin : ∀ q : AlgebraProjection P,q ≤ pP → q.val=0 ∨ q.val=p := by
    intro q hq
    by_cases hq0 : q.val=0
    · exact Or.inl hq0
    by_cases hqp : q.val=p
    · exact Or.inr hqp
    exact False.elim (hn ⟨q.val,q.property,hq0,hqp,hq,projection_mul_of_le hq⟩)
  let pM := includedProjection hPM pP
  have hpM0 : pM.val ≠ 0 := by
    intro h
    apply hp0
    exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff pM.val pM.property hpM0
  let Q : StarSubalgebra ℂ M.toStarSubalgebra := insideAlgebra (M := M) (P := P)
  have hirrQ : ∀ c : M.toStarSubalgebra,
      (∀ a : Q,(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hPM a,a.property⟩)
  have hcomm : ∀ a : Q,Commute q (pM.val*(a : M.toStarSubalgebra)*pM.val) := by
    intro a
    let aP : P.toStarSubalgebra := ⟨a.val.val,a.property⟩
    obtain ⟨z,hz⟩ := corner_scalar_of_projections pP hmin (p*aP*p)
      (by change p*(p*aP*p)=p*aP*p; simp only [← mul_assoc,hp.isIdempotentElem.eq])
      (by change (p*aP*p)*p=p*aP*p; simp only [mul_assoc,hp.isIdempotentElem.eq])
    have he : pM.val*(a : M.toStarSubalgebra)*pM.val=z • pM.val := by
      exact Subtype.ext (congrArg (fun b : P.toStarSubalgebra => b.val) hz)
    rw [he]
    show q*(z • pM.val)=(z • pM.val)*q
    rw [mul_smul_comm,smul_mul_assoc,hqp',hpq]
  exact (corner_commutant_projection_trivial τ Q hirrQ pM ⟨q,hq⟩ hpq hcomm).elim hq0 hqp

theorem tracial_isometry_coisometry (τ : TracialRepresentation M)
    (v : M.toStarSubalgebra) (hv : star v*v=1) : v*star v=1 := by
  let p : AlgebraProjection M := ⟨v*star v,by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = v*(star v*v)*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hv,mul_one]
    · simp only [IsSelfAdjoint,star_mul,star_star]⟩
  have ht : τ.trace p.val=τ.trace (identityProjection M).val := by
    change τ.trace (v*star v)=τ.trace 1
    rw [τ.trace_mul_comm,hv]
  have h := projection_eq_of_le_of_trace_eq τ (p := p) (q := identityProjection M)
    (one_mul _) ht
  exact congrArg Subtype.val h

theorem tracial_nonzero (τ : TracialRepresentation M) : (0 : H →L[ℂ] H) ≠ 1 := by
  intro h
  have hzero : τ.vector=0 := by
    have he := congrArg (fun T : H →L[ℂ] H => T τ.vector) h
    exact he.symm
  have hn := τ.norm_vector
  rw [hzero,norm_zero] at hn
  exact zero_ne_one hn

end Generator.Tracial

end

end OAI
