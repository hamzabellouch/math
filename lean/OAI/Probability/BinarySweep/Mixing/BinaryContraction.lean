import Mathlib
import OAI.Probability.BinarySweep.Analytic.AnalyticTransfer
import OAI.Probability.BinarySweep.GridBounds.GridLaw
import OAI.Probability.BinarySweep.FiniteLaws.BitBlocks

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma averageOperator_sum {G : Type*} [Fintype G] [Monoid G] {D : ℕ}
    (p : G → ℝ) (ρ : Representation ℂ G (RepSpace D)) :
    averageOperator p ρ=∑g,(p g:ℂ) • Module.End.toContinuousLinearMap (RepSpace D) (ρ g) := by
  apply ContinuousLinearMap.coe_injective
  simp [averageOperator,Module.End.toContinuousLinearMap]

lemma pushLaw_complex_expectation {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [Module ℂ R] (p : A → ℝ) (f : A → B) (F : B → R) :
    (∑b,(pushLaw p f b:ℂ) • F b)=∑a,(p a:ℂ) • F (f a) := by
  unfold pushLaw
  simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,Finset.sum_smul]
  rw [Finset.sum_comm]
  simp [ite_smul]

lemma gridAverage_relabel {b D d : ℕ} (bits : Fin b → ℕ) (e : GridSlot bits ≃ Slot d)
    (ρ : Representation ℂ (Equiv.Perm (Slot d)) (RepSpace D))
    (he : pushLaw (gridLaw bits) e.permCongr=binaryLaw d) :
    complexGridAverage bits (ρ.comp e.permCongrHom.toMonoidHom) 1=
      averageOperator (binaryLaw d) ρ := by
  rw [averageOperator_sum,←he,pushLaw_complex_expectation]
  unfold gridLaw
  rw [pushLaw_complex_expectation]
  unfold complexGridAverage
  apply Finset.sum_congr rfl
  intro c _
  rw [show (1:ℂ)=(1:ℝ) from rfl,complexGridWeight_real]
  rfl

theorem binary_contraction : BinaryContractionTarget := by
  obtain ⟨r,hr,g,hg,hgrid⟩ := grid_analytic_contraction
  refine ⟨g,hg,r,?_⟩
  intro d hd D ρ hi hu
  have := hi
  obtain ⟨b,hb,bits,hbits,hsum⟩ := exists_bit_blocks r hr d hd
  obtain ⟨d',hd',e,he⟩ := gridLaw_binary b hb bits
  have hdd : d'=d := hd'.trans hsum
  cases hdd
  have hσ : Representation.IsIrreducible (ρ.comp e.permCongrHom.toMonoidHom) :=
    Irrep.irreducible_comp_equiv e.permCongrHom ρ
  have hunit : IsUnitaryRep (ρ.comp e.permCongrHom.toMonoidHom) := fun g v => hu _ _
  have hh := hgrid b hb bits hbits D (ρ.comp e.permCongrHom.toMonoidHom) hσ hunit
  rwa [gridAverage_relabel bits e ρ he] at hh

open Irrep

variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma complexAverage_transport (ρ : Representation ℂ G V) (p : G → ℂ)
    (v : V) :
    (stdOrthonormalBasis ℂ V).repr (complexAverage ρ p v)=
      complexAverage (conjugateRep ρ (stdOrthonormalBasis ℂ V).repr.toLinearEquiv) p
        ((stdOrthonormalBasis ℂ V).repr v) := by
  simp only [complexAverage_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change _ = (stdOrthonormalBasis ℂ V).repr
    (ρ g ((stdOrthonormalBasis ℂ V).repr.symm ((stdOrthonormalBasis ℂ V).repr v)))
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma hilbert_norm_of_coordinates (ρ : Representation ℂ G V) (p : G → ℂ) {a : ℝ}
    (ha : 0≤a)
    (h : ‖complexAverage (conjugateRep ρ (stdOrthonormalBasis ℂ V).repr.toLinearEquiv) p‖≤a) :
    ‖complexAverage ρ p‖≤a := by
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro v
  rw [←(stdOrthonormalBasis ℂ V).repr.norm_map (complexAverage ρ p v),
    complexAverage_transport]
  exact ((complexAverage _ _).le_opNorm _).trans (by
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem binary_hilbert_contraction : ∃ g : ℝ, 0<g ∧ ∃ d₀ : ℕ,
    ∀ d ≥ d₀, ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V), ρ.IsIrreducible →
      (∀g v, ‖ρ g v‖=‖v‖) →
      ‖complexAverage ρ (fun g => (binaryLaw d g:ℂ))‖≤(Module.finrank ℂ V:ℝ)^(-g) := by
  obtain ⟨g,hg,d₀,hh⟩ := binary_contraction
  refine ⟨g,hg,d₀,?_⟩
  intro d hd V _ _ _ ρ hi hu
  let := hi
  let E := (stdOrthonormalBasis ℂ V).repr
  let σ := conjugateRep ρ E.toLinearEquiv
  have hσ : σ.IsIrreducible := irreducible_equiv ρ σ (conjugateEquiv ρ E.toLinearEquiv)
  have hunit : IsUnitaryRep σ := by
    intro g v
    change ‖E (ρ g (E.symm v))‖=‖v‖
    rw [E.norm_map,hu,E.symm.norm_map]
  exact hilbert_norm_of_coordinates ρ _ (by positivity) (hh d hd _ σ hσ hunit)

lemma evenMoment_one_norm_bound (A : V →L[ℂ] V) {a : ℝ} (_ha : 0≤a) (hA : ‖A‖≤a) :
    evenMoment 1 A.toLinearMap ≤ (Module.finrank ℂ V:ℝ)*a^2 := by
  let e := stdOrthonormalBasis ℂ V
  unfold evenMoment
  rw [pow_one,LinearMap.trace_eq_sum_inner _ e,Complex.re_sum]
  calc
    _ ≤ ∑i : Fin (Module.finrank ℂ V),a^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Module.End.mul_apply,LinearMap.adjoint_inner_right]
      have hn : ‖e i‖=1 := e.orthonormal.1 i
      have hb := (A.le_opNorm (e i)).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      rw [hn,mul_one] at hb
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := by simp

lemma complexAverage_uniform_zero (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hD : 1<Module.finrank ℂ V) :
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))=0 := by
  apply ContinuousLinearMap.coe_injective
  change groupAverage ρ _ = 0
  simp only [groupAverage,uniformLaw,Complex.ofReal_inv,Complex.ofReal_natCast,
    ←Finset.smul_sum,Irrep.sum_eq_zero_of_finrank_gt_one ρ hD,smul_zero]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma swap_tabloid_eq {I : Type*} [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) (i j : I) (c : C μ) :
    tabloidOfPerm μ (Equiv.swap a (u i)*c.val)=tabloidOfPerm μ (Equiv.swap a (u j)) ↔
      i=j ∧ c=1 := by
  have hau (i : I) : a≠u i := fun he => ha (he ▸ hu i)
  constructor
  · intro he
    have hij : i=j := by
      by_contra hij
      have huij : u j≠u i := fun hh => hij (u.injective hh).symm
      have hju : u j≠a := (hau j).symm
      have hh := congrArg (fun t : Tabloid μ => t.val (u j)) he
      have hc := hfix c⁻¹ j
      have hs : Equiv.swap a (u i) (u j)=u j := Equiv.swap_apply_of_ne_of_ne hju huij
      simp only [tabloidOfPerm,labels,mul_inv_rev,Equiv.swap_inv,
        Equiv.Perm.mul_apply,hs,Equiv.swap_apply_right] at hh
      change row (c.val⁻¹ (u j))=row a at hh
      rw [show c.val⁻¹ (u j)=u j from hc,hu] at hh
      exact ha hh.symm
    subst j
    have hc : c.val⁻¹ ∈ rowStabilizer μ := by
      have hh := (tabloidOfPerm_eq_iff μ _ _).mp he
      simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hc' : c.val ∈ rowStabilizer μ := by
      simpa using (rowStabilizer μ).inv_mem hc
    have hh : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc',c.property⟩
    rw [row_col_intersection] at hh
    exact ⟨rfl,Subtype.ext hh⟩
  · rintro ⟨rfl,rfl⟩
    simp

lemma swap_poly_coefficient {I : Type*} [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) (i j : I) :
    tabloidRepresentation μ (Equiv.swap a (u i)) (polytabloid μ)
      (tabloidOfPerm μ (Equiv.swap a (u j)))=if i=j then (1:ℂ) else 0 := by
  rw [polytabloid,columnAnti_apply]
  simp_rw [rep_basis,smul_tabloidOfPerm,mul_one]
  rw [map_sum]
  simp_rw [map_smul,rep_basis,smul_tabloidOfPerm]
  simp only [Finset.sum_apply,Pi.smul_apply,tabloidBasis,Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ (Equiv.swap a (u j))=
      tabloidOfPerm μ (Equiv.swap a (u i)*c.val) ↔ i=j ∧ c=1 :=
    eq_comm.trans (swap_tabloid_eq μ a ha u hu hfix i j c)
  simp only [he]
  by_cases hij : i=j <;> simp [hij]

theorem singleton_column_dimension {I : Type*} [Fintype I] [DecidableEq I]
    (a : Cell μ) (ha : row a≠0) (u : I ↪ Cell μ) (hu : ∀i,row (u i)=0)
    (hfix : ∀c : C μ, ∀i,c.val (u i)=u i) :
    Fintype.card I ≤ Module.finrank ℂ (SpechtSpace μ) := by
  have hind : LinearIndependent ℂ
      (fun i : I => spechtRep μ (Equiv.swap a (u i)) (spechtPoly μ)) := by
    apply LinearIndependent.of_comp (f:=spechtInclude μ)
    rw [Fintype.linearIndependent_iff]
    intro t ht j
    have hh := congrFun ht (tabloidOfPerm μ (Equiv.swap a (u j)))
    simp only [Finset.sum_apply,Pi.smul_apply,Function.comp_apply,Pi.zero_apply] at hh
    simp_rw [spechtInclude_rep,spechtInclude_poly,swap_poly_coefficient μ a ha u hu hfix] at hh
    simpa using hh
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact hind.fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

end OAI
