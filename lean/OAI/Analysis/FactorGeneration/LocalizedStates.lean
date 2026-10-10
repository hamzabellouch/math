import OAI.Analysis.FactorGeneration.SpectralStates

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology
section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace AlgebraProjection

/-- A continuous orthogonally additive real charge nonnegative on G admits a
nonzero corner all of whose subprojections have nonnegative charge. -/
theorem exists_nonnegative_corner
    (μ : AlgebraProjection M → ℝ)
    (hadd : ∀ p q (ho : p.val*q.val=0), μ (orthogonalSum p q ho)=μ p+μ q)
    (hcont : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (a : I → AlgebraProjection M), Monotone a →
      ∀ p, IsLUB (Set.range a) p → Tendsto (fun i => μ (a i)) atTop (𝓝 (μ p)))
    (G : AlgebraProjection M) (hG : G.val≠0) (hμG : 0 ≤ μ G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F → 0 ≤ μ p := by
  classical
  by_cases hall : ∀ p : AlgebraProjection M, p ≤ G → 0 ≤ μ p
  · exact ⟨G,le_rfl,hG,hall⟩
  push Not at hall
  obtain ⟨r,hrG,hr⟩ := hall
  let S : Set (AlgebraProjection M) := {p | p ≤ G ∧ μ p ≤ μ r}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · let : Nonempty c := hne.to_subtype
      let : IsDirected c (· ≤ ·) := ⟨by
        intro a b
        rcases hchain.total a.property b.property with h | h
        · exact ⟨b,h,le_rfl⟩
        · exact ⟨a,le_rfl,h⟩⟩
      obtain ⟨p,hp⟩ := exists_isLUB_monotone (fun q : c => q.val) (fun _ _ h => h)
      refine ⟨p,⟨?_,?_⟩,fun q hq => hp.1 ⟨⟨q,hq⟩,rfl⟩⟩
      · exact hp.2 (by rintro _ ⟨q,rfl⟩; exact (hc q.property).1)
      · exact le_of_tendsto (hcont c (fun q : c => q.val) (fun _ _ h => h) p hp)
          (Eventually.of_forall (fun q => (hc q.property).2))
    · exact ⟨r,⟨hrG,le_rfl⟩,fun q hq => (hne ⟨q,hq⟩).elim⟩)
  have hvG : v ≤ G := hv.1.1
  have hvneg : μ v < 0 := hv.1.2.trans_lt hr
  let F := remainder v G hvG
  have hF : F.val≠0 := by
    intro hz
    have he : G=v := Subtype.ext (sub_eq_zero.mp hz)
    rw [he] at hμG
    exact (not_lt_of_ge hμG) hvneg
  refine ⟨F,remainder_le v G hvG,hF,?_⟩
  intro p hp
  by_contra hnot
  have hpneg : μ p<0 := lt_of_not_ge hnot
  have ho : v.val*p.val=0 := projection_orthogonal_of_le
    (remainder_orthogonal v G hvG) le_rfl hp
  let q := orthogonalSum v p ho
  have hqG : q ≤ G := orthogonalSum_le ho hvG (hp.trans (remainder_le v G hvG))
  have he : μ q=μ v+μ p := hadd v p ho
  have hqμ : μ q ≤ μ r := by linarith [hv.1.2]
  have hqv : q ≤ v := hv.2 ⟨hqG,hqμ⟩ (le_orthogonalSum_left _ _ ho)
  have hqeq : q=v := le_antisymm hqv (le_orthogonalSum_left _ _ ho)
  rw [hqeq] at he
  linarith

end AlgebraProjection

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_tendsto_monotone
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    Tendsto (fun i => traceFreeDimension hfactor hdiff (q i)) atTop
      (𝓝 (traceFreeDimension hfactor hdiff p)) := by
  rw [traceFreeDimension_isLUB_monotone hfactor hdiff hfinite hunit q hq p hp]
  exact tendsto_atTop_isLUB ((traceFreeDimension_mono hfactor hdiff).comp hq)
    (isLUB_csSup (Set.range_nonempty _) (traceFreeDimension_range_bddAbove hfactor hdiff q))

include hfinite in
/-- Concrete localization for a real linear combination of the actual vector
functional and the already constructed dimension; no linear trace is assumed. -/
theorem exists_signed_vector_dimension_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (c d : ℝ) (G : AlgebraProjection M) (hG : G.val≠0)
    (hμG : 0 ≤ c*G.vectorValue ξ+d*traceFreeDimension hfactor hdiff G) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧
      ∀ p, p ≤ F → 0 ≤ c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p := by
  apply AlgebraProjection.exists_nonnegative_corner
    (fun p => c*p.vectorValue ξ+d*traceFreeDimension hfactor hdiff p) ?_ ?_ G hG hμG
  · intro p q ho
    have hν : (orthogonalSum p q ho).vectorValue ξ=p.vectorValue ξ+q.vectorValue ξ := by
      change (inner ℂ ξ (p.val.val ξ+q.val.val ξ)).re=_
      rw [inner_add_right,Complex.add_re]
      rfl
    have hD := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p q hunit (one_mul _) (one_mul _) ho
    change traceFreeDimension hfactor hdiff (orthogonalSum p q ho)=
      traceFreeDimension hfactor hdiff p+traceFreeDimension hfactor hdiff q at hD
    rw [hν,hD]
    ring
  · intro I _ _ _ a ha p hp
    exact ((AlgebraProjection.vectorValue_tendsto_monotone a ha p hp ξ).const_mul c).add
      ((traceFreeDimension_tendsto_monotone hfactor hdiff hfinite hunit a ha p hp).const_mul d)

include hfinite in
theorem exists_vector_dimension_lower_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      G.vectorValue ξ*traceFreeDimension hfactor hdiff p ≤
        p.vectorValue ξ*traceFreeDimension hfactor hdiff G := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (traceFreeDimension hfactor hdiff G) (-G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

include hfinite in
theorem exists_vector_dimension_upper_corner
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (G : AlgebraProjection M) (hG : G.val≠0) :
    ∃ F : AlgebraProjection M, F ≤ G ∧ F.val≠0 ∧ ∀ p, p ≤ F →
      p.vectorValue ξ*traceFreeDimension hfactor hdiff G ≤
        G.vectorValue ξ*traceFreeDimension hfactor hdiff p := by
  obtain ⟨F,hFG,hF,h⟩ := exists_signed_vector_dimension_corner hfactor hdiff hfinite hunit
    ξ (-traceFreeDimension hfactor hdiff G) (G.vectorValue ξ) G hG (by nlinarith)
  exact ⟨F,hFG,hF,fun p hp => by have hh := h p hp; nlinarith⟩

end

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- An actual unit vector admits a nonzero corner on which every projection
value is between a D(p) and (1+ε)a D(p), with a strictly positive. -/
theorem exists_vector_dimension_localization
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ p : AlgebraProjection M, p ≤ E →
        a*traceFreeDimension hfactor hdiff p ≤ (inner ℂ ξ (p.val.val ξ)).re ∧
        (inner ℂ ξ (p.val.val ξ)).re ≤ (1+ε)*a*traceFreeDimension hfactor hdiff p := by
  classical
  let ν := AlgebraProjection.vectorValue (M := M) ξ
  let D := traceFreeDimension hfactor hdiff
  let oneP : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  have hν1 : ν oneP=1 := by
    change (inner ℂ ξ ξ).re=1
    rw [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hD1 : D oneP=1 := traceFreeDyadicSup_self hfactor hdiff oneP
  have hDpos (p : AlgebraProjection M) (hp : p.val≠0) : 0<D p :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite oneP p hp
  obtain ⟨F,_,hF,hlo⟩ := exists_vector_dimension_lower_corner
    hfactor hdiff hfinite hunit ξ oneP hunit
  have hFbound (p : AlgebraProjection M) (hp : p ≤ F) : D p ≤ ν p := by
    have hh := hlo p hp
    change ν oneP*D p ≤ ν p*D oneP at hh
    simpa only [hν1,hD1,one_mul,mul_one] using hh
  let R : Set ℝ := {b | ∃ p : AlgebraProjection M, p ≤ F ∧ p.val≠0 ∧ b=ν p/D p}
  have hRne : R.Nonempty := ⟨ν F/D F,F,le_rfl,hF,rfl⟩
  have hRlower : ∀ b ∈ R, 1 ≤ b := by
    rintro b ⟨p,hp,hpn,rfl⟩
    exact (le_div_iff₀ (hDpos p hpn)).mpr (by simpa only [one_mul] using hFbound p hp)
  have hRb : BddBelow R := ⟨1,hRlower⟩
  let a := sInf R
  have ha1 : 1 ≤ a := le_csInf hRne hRlower
  have ha : 0<a := lt_of_lt_of_le (by norm_num) ha1
  have hnear : a < (1+ε)*a := by nlinarith
  obtain ⟨_,⟨r,hrF,hr,hratio⟩,hnearR⟩ := exists_lt_of_csInf_lt hRne hnear
  rw [hratio] at hnearR
  obtain ⟨E,hEr,hE,hhi⟩ := exists_vector_dimension_upper_corner
    hfactor hdiff hfinite hunit ξ r hr
  refine ⟨E,a,hE,ha,?_⟩
  intro p hp
  by_cases hp0 : p.val=0
  · have hν0 : ν p=0 := by
      change (inner ℂ ξ (p.val.val ξ)).re=0
      rw [hp0]
      simp
    have hD0 : D p=0 := traceFreeDyadicSup_zero hfactor hdiff oneP p hunit hp0
    change a*D p ≤ ν p ∧ ν p ≤ (1+ε)*a*D p
    rw [hν0,hD0]
    simp
  · have hDp : 0<D p := hDpos p hp0
    have hpF : p ≤ F := hp.trans (hEr.trans hrF)
    have hap : a ≤ ν p/D p := csInf_le hRb ⟨p,hpF,hp0,rfl⟩
    have hloP : a*D p ≤ ν p := (le_div_iff₀ hDp).mp hap
    have hDr : 0<D r := hDpos r hr
    have hhiP := hhi p hp
    change ν p*D r ≤ ν r*D p at hhiP
    have hratioP : ν p ≤ (ν r/D r)*D p := by
      apply (mul_le_mul_iff_right₀ hDr).mp
      calc D r*ν p = ν p*D r := mul_comm _ _
           _ ≤ ν r*D p := hhiP
           _ = D r*(ν r/D r*D p) := by field_simp
    have hbound : (ν r/D r)*D p ≤ (1+ε)*a*D p :=
      mul_le_mul_of_nonneg_right hnearR.le hDp.le
    exact ⟨hloP,hratioP.trans hbound⟩

end

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerValuePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

/-- The actual bounded complex-linear vector functional on the original algebra. -/
def vectorFunctional (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => inner ℂ ξ (x.val ξ)
      map_add' := fun x y => inner_add_right _ _ _
      map_smul' := fun c x => inner_smul_right _ _ _ }
    (‖ξ‖^2) (fun x => by
      calc ‖inner ℂ ξ (x.val ξ)‖ ≤ ‖ξ‖*‖x.val ξ‖ := norm_inner_le_norm _ _
           _ ≤ ‖ξ‖*(‖x.val‖*‖ξ‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm ξ) (norm_nonneg _)
           _ = ‖ξ‖^2*‖x‖ := by change ‖ξ‖*(‖x‖*‖ξ‖)=_; ring)

theorem vectorFunctional_apply (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ x=inner ℂ ξ (x.val ξ) := rfl

theorem vectorFunctional_norm_le (ξ : H) : ‖vectorFunctional (M := M) ξ‖ ≤ ‖ξ‖^2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- A positive operator supported by p is approximated inside that same corner. -/
theorem exists_positive_corner_spectral_approximation
    (p : AlgebraProjection M) (x : M.toStarSubalgebra) (hx : 0 ≤ x)
    (hpx : p.val*x=x) (ε : ℝ) (hε : 0<ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧ (∀ i, Commute (Q.piece i).val x) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  have hxp : x*p.val=x := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hpx
  let I : SpectralInterval x :=
    { proj := p
      lo := 0
      hi := ‖x‖
      lower := by simpa only [hpx,hxp,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval p x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro i
    exact I.partition_commutes hx.isSelfAdjoint (Commute.refl x) (hpx.trans hxp.symm) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖p.val*x*p.val-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [hpx,hxp] using hn

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.corner_bound
    {x : M.toStarSubalgebra} {t : ℂ} (ht : IsDimensionSpectralValue hfactor hdiff x t)
    (p : AlgebraProjection M) (hpx : Commute p.val x)
    (Q : CornerPartition p) (c : Fin Q.size → ℂ) (hc : ∀ i, Commute (Q.piece i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (Q.piece i).val‖ := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let q : Fin Q.size ⊕ Unit → AlgebraProjection M := Sum.elim Q.piece (fun _ => r)
  let d : Fin Q.size ⊕ Unit → ℂ := Sum.elim c (fun _ => 0)
  have ho (i j : Fin Q.size ⊕ Unit) (h : i≠j) : (q i).val*(q j).val=0 := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact Q.orthogonal i j (fun he => h (congrArg Sum.inl he))
      | inr j =>
        change (Q.piece i).val*(1-p.val)=0
        rw [mul_sub,mul_one,projection_mul_of_le (Q.piece_le i),sub_self]
    | inr i =>
      cases j with
      | inl j =>
        change (1-p.val)*(Q.piece j).val=0
        rw [sub_mul,one_mul,show p.val*(Q.piece j).val=(Q.piece j).val from Q.piece_le j,sub_self]
      | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    simp only [q,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,Q.total]
    change p.val+(1-p.val)=1
    abel
  have hqc (i : Fin Q.size ⊕ Unit) : Commute (q i).val x := by
    cases i with
    | inl i => exact hc i
    | inr i => exact (Commute.one_left x).sub_left hpx
  have hh := ht.family_bound hfactor hdiff q ho hs d hqc
  simpa only [q,d,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,zero_mul,zero_smul,
    Finset.sum_const_zero,add_zero] using hh

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance localizedCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance localizedOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance localizedPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance localizedLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance localizedStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem positive_functional_bounds_of_projection_bounds
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (E : AlgebraProjection M)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hproj : ∀ p : AlgebraProjection M, p ≤ E →
      a*traceFreeDimension hfactor hdiff p ≤ (φ p.val).re ∧
      (φ p.val).re ≤ b*traceFreeDimension hfactor hdiff p)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hEx : E.val*x=x) :
    a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤ (φ x).re ∧
      (φ x).re ≤ b*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  have hxE : x*E.val=x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq,hx.isSelfAdjoint.star_eq]
      using congrArg star hEx
  have happrox (ε : ℝ) (hε : 0<ε) :
      a*t.re ≤ (φ x).re+ε ∧ (φ x).re ≤ b*t.re+ε := by
    let C := a+b+‖φ‖+1
    have hC : 0<C := by dsimp [C]; positivity
    let δ := ε/C
    have hδ : 0<δ := div_pos hε hC
    have hCδ : C*δ=ε := mul_div_cancel₀ _ hC.ne'
    obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_corner_spectral_approximation E x hx hEx δ hδ
    let y : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
    let v : ℝ := (φ y).re
    have hw : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
      simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
    have hv : v=∑ i, c i*(φ (Q.piece i).val).re := by
      simp only [v,y,map_sum,map_smul,smul_eq_mul,Complex.re_sum,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hav : a*w ≤ v := by
      rw [hv,show a*w=∑ i, c i*(a*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).1 (hc i))
    have hvb : v ≤ b*w := by
      rw [hv,show b*w=∑ i, c i*(b*traceFreeDimension hfactor hdiff (Q.piece i)) by
        simp only [w,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hproj (Q.piece i) (Q.piece_le i)).2 (hc i))
    have hspec := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2.corner_bound
      hfactor hdiff E (hEx.trans hxE.symm) Q (fun i => (c i : ℂ)) hQ
    have htw : |t.re-w| ≤ δ := by
      have h := Complex.abs_re_le_norm (t-(w : ℂ))
      rw [Complex.sub_re,Complex.ofReal_re] at h
      apply h.trans
      rw [hw]
      exact hspec.trans herr.le
    have hφ : |(φ x).re-v| ≤ ‖φ‖*δ := by
      have he : (φ x).re-v=(φ (x-y)).re := by rw [map_sub,Complex.sub_re]
      rw [he]
      exact (Complex.abs_re_le_norm _).trans ((φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left herr.le (norm_nonneg φ)))
    have htw' := abs_le.mp htw
    have hφ' := abs_le.mp hφ
    have had := mul_nonneg ha hδ.le
    have hbd := mul_nonneg hb hδ.le
    dsimp only [C] at hCδ
    constructor <;> nlinarith
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).1
  · apply le_of_forall_pos_le_add
    intro ε hε
    exact (happrox ε hε).2

/-- Concrete projection and positive-operator localization, with an actual
bounded complex-linear functional and a nonzero constructed corner. -/
theorem exists_localized_vector_functional
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (E : AlgebraProjection M) (a : ℝ), E.val≠0 ∧ 0<a ∧
      ∀ (x : M.toStarSubalgebra) (hx : 0 ≤ x), E.val*x=x →
        a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re ≤
          (vectorFunctional ξ x).re ∧
        (vectorFunctional ξ x).re ≤
          (1+ε)*a*(dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  obtain ⟨E,a,hE,ha,hp⟩ := exists_vector_dimension_localization hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,a,hE,ha,?_⟩
  intro x hx hEx
  exact positive_functional_bounds_of_projection_bounds hfactor hdiff hfinite hunit
    (vectorFunctional ξ) E a ((1+ε)*a) ha.le (mul_nonneg (by linarith) ha.le) hp x hx hEx

end

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerStatePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem exists_unit_vector_of_unit_ne_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ ξ : H, ‖ξ‖=1 := by
  classical
  have hne : ∃ ξ : H, ξ≠0 := by
    by_contra h
    push Not at h
    apply hunit
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hne
  refine ⟨(‖ξ‖⁻¹ : ℂ) • ξ,?_⟩
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg ξ),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]

theorem vectorFunctional_star_mul_self (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ (star x*x)=(‖x.val ξ‖^2 : ℂ) := by
  change inner ℂ ξ (star x.val (x.val ξ))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem vectorFunctional_positive (ξ : H) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (vectorFunctional ξ x).re := by
  let b := CFC.sqrt x
  have hb : star b=b := (CFC.sqrt_nonneg x).isSelfAdjoint.star_eq
  have he : star b*b=x := by rw [hb]; exact CFC.sqrt_mul_sqrt_self x hx
  rw [← he,vectorFunctional_star_mul_self]
  norm_cast
  positivity

theorem vectorFunctional_one (ξ : H) (hξ : ‖ξ‖=1) :
    vectorFunctional (M := M) ξ 1=1 := by
  change inner ℂ ξ ξ=1
  rw [inner_self_eq_norm_sq_to_K,hξ]
  norm_num

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- A localized vector functional is nearly cyclic for every element in its
corner. This gives both inequalities by applying the result to x and x*. -/
theorem exists_corner_nearly_cyclic_vector
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (ξ : H) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ E : AlgebraProjection M, E.val≠0 ∧
      (∀ p : AlgebraProjection M, p ≤ E → p.val≠0 → 0<(vectorFunctional ξ p.val).re) ∧
      ∀ x : M.toStarSubalgebra, E.val*x=x → x*E.val=x →
        (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re := by
  obtain ⟨E,a,hE,ha,h⟩ := exists_localized_vector_functional
    hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨E,hE,?_,?_⟩
  · intro p hp hpn
    have hpstar : star p.val*p.val=p.val := by
      rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
    have hpnonneg : 0 ≤ p.val := hpstar ▸ star_mul_self_nonneg p.val
    have hh := (h p.val hpnonneg hp).1
    rw [dimensionSpectralValue_projection,Complex.ofReal_re] at hh
    exact (mul_pos ha (traceFreeDyadicSup_pos hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ p hpn)).trans_le hh
  intro x hEx hxE
  have hExs : E.val*star x=star x := by
    simpa only [star_mul,E.property.isSelfAdjoint.star_eq] using congrArg star hxE
  have h₁ := h (star x*x) (star_mul_self_nonneg x) (by rw [← mul_assoc,hExs])
  have h₂ := h (x*star x) (mul_star_self_nonneg x) (by rw [← mul_assoc,hEx])
  have he := congrArg Complex.re (dimensionSpectralValue_star_mul_self hfactor hdiff hfinite hunit x)
  have hm := mul_le_mul_of_nonneg_left h₂.1 (by linarith : 0 ≤ 1+ε)
  rw [← he] at hm
  nlinarith [h₁.2]

include hfactor hdiff hfinite in
/-- Entirely constructed from the original finite diffuse factor fields:
a positive unital bounded linear functional, and a nonzero nearly cyclic corner. -/
theorem exists_nearly_cyclic_corner_state
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ (φ : M.toStarSubalgebra →L[ℂ] ℂ) (E : AlgebraProjection M),
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      E.val≠0 ∧ (∀ p : AlgebraProjection M, p ≤ E → p.val≠0 → 0<(φ p.val).re) ∧ ∀ x : M.toStarSubalgebra, E.val*x=x → x*E.val=x →
        (φ (star x*x)).re ≤ (1+ε)*(φ (x*star x)).re := by
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,hE,hfaith,h⟩ := exists_corner_nearly_cyclic_vector hfactor hdiff hfinite hunit ξ hξ ε hε
  refine ⟨vectorFunctional ξ,E,?_,vectorFunctional_one ξ hξ,vectorFunctional_positive ξ,hE,hfaith,h⟩
  simpa only [hξ,one_pow] using vectorFunctional_norm_le (M := M) ξ

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem compose_base_target (E : EquivalentPartition p ι) (v : PartialIsometry M)
    (hv : v.target=E.base) (i : ι) :
    ((E.leg i).compose v (by rw [hv,E.initial])).target=(E.leg i).target := by
  apply Subtype.ext
  rw [PartialIsometry.compose_target,hv,← E.initial i,(E.leg i).mul_support]
  rfl

/-- Change the common initial corner by a displayed equivalence. -/
def rebase (E : EquivalentPartition p ι) (v : PartialIsometry M) (hv : v.target=E.base) :
    EquivalentPartition p ι where
  base := v.support
  leg i := (E.leg i).compose v (by rw [hv,E.initial])
  initial _ := rfl
  cross i j hij := by
    change star ((E.leg i).val*v.val)*((E.leg j).val*v.val)=0
    calc _ = star v.val*(star (E.leg i).val*(E.leg j).val)*v.val := by
           simp only [star_mul,mul_assoc]
         _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]
  total := by simpa only [E.compose_base_target v hv] using E.total
  bound i := by rw [E.compose_base_target v hv]; exact E.bound i

theorem base_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) : E.base.val≠0 := by
  intro hz
  have hl (i : ι) : (E.leg i).val=0 := by
    have h := (E.leg i).mul_support
    rw [E.initial,hz,mul_zero] at h
    exact h.symm
  have ht := E.total
  have hz' (i : ι) : (E.leg i).target.val=0 := by
    change (E.leg i).val*star (E.leg i).val=0
    rw [hl,zero_mul]
  rw [show (∑ i, (E.leg i).target.val)=0 from Finset.sum_eq_zero (fun i _ => hz' i)] at ht
  exact hp ht.symm

end EquivalentPartition

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- Every actual finite equivalent partition has the expected base dimension. -/
theorem EquivalentPartition.dimension_base
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {p : AlgebraProjection M} {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : EquivalentPartition p ι) :
    traceFreeDimension hfactor hdiff E.base=traceFreeDimension hfactor hdiff p/Fintype.card ι := by
  have he (i : ι) : traceFreeDimension hfactor hdiff (E.leg i).target=
      traceFreeDimension hfactor hdiff E.base :=
    (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show E.base.Equivalent (E.leg i).target from ⟨E.leg i,E.initial i,rfl⟩)).symm
  have h := traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => (E.leg i).target) E.orthogonal p E.total
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℝ)≠0)).mpr
  linarith

include hfactor hdiff hfinite in
/-- A partition of 1 with common initial projection inside any given nonzero E. -/
theorem exists_equivalent_partition_base_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (E : AlgebraProjection M) (hE : E.val≠0) :
    ∃ (n : ℕ) (_hn : 0<n)
      (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) (Fin n)),
      Q.base ≤ E ∧ Q.base.val≠0 := by
  have hD : 0<traceFreeDimension hfactor hdiff E :=
    traceFreeDyadicSup_pos hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ E hE
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hD (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hn0 : 0<2^n := Nat.two_pow_pos n
  let Q := Classical.choice (traceFreeDimension_exists_equivalent_partition
    hfactor hdiff hfinite hunit (2^n) hn0 ⟨1,IsStarProjection.one _⟩)
  have : Nonempty (Fin (2^n)) := ⟨⟨0,hn0⟩⟩
  have hQ : traceFreeDimension hfactor hdiff Q.base=1/2^n := by
    rw [Q.dimension_base hfactor hdiff hfinite hunit]
    have h1 : traceFreeDimension hfactor hdiff (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M)=1 :=
      traceFreeDyadicSup_self hfactor hdiff ⟨1,IsStarProjection.one _⟩
    rw [h1]
    simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  obtain ⟨v,hv,ht⟩ := (traceFreeDimension_le_iff_subequivalent hfactor hdiff hfinite hunit Q.base E).mp
    (by rw [hQ]; exact hn.le)
  have hvt : v.adjoint.target=Q.base := by
    apply Subtype.ext
    change star v.val*star (star v.val)=Q.base.val
    rw [star_star,v.initial,hv]
  let R := Q.rebase v.adjoint hvt
  exact ⟨2^n,hn0,R,ht,R.base_ne_zero hunit⟩

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-- Matrix coefficient in the common initial corner. -/
def stateCoefficient (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    M.toStarSubalgebra := star (Q.leg i).val*x*(Q.leg j).val

theorem stateCoefficient_left (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.base.val*Q.stateCoefficient x i j=Q.stateCoefficient x i j := by
  have hs : Q.base.val*star (Q.leg i).val=star (Q.leg i).val := by
    have h := congrArg star (Q.leg i).mul_support
    simpa only [star_mul,Q.initial,Q.base.property.isSelfAdjoint.star_eq] using h
  change Q.base.val*(star (Q.leg i).val*x*(Q.leg j).val)=_
  rw [← mul_assoc,← mul_assoc,hs]
  rfl

theorem stateCoefficient_right (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient x i j*Q.base.val=Q.stateCoefficient x i j := by
  change (star (Q.leg i).val*x*(Q.leg j).val)*Q.base.val=_
  rw [mul_assoc,← Q.initial j,(Q.leg j).mul_support]
  rfl

theorem stateCoefficient_star (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    star (Q.stateCoefficient x i j)=Q.stateCoefficient (star x) j i := by
  simp only [stateCoefficient,star_mul,star_star,mul_assoc]

theorem stateCoefficient_mul (Q : EquivalentPartition p ι) (hp : p.val=1)
    (x y : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient (x*y) i j=∑ k, Q.stateCoefficient x i k*Q.stateCoefficient y k j := by
  have he (k : ι) : Q.stateCoefficient x i k*Q.stateCoefficient y k j=
      star (Q.leg i).val*x*(Q.leg k).target.val*y*(Q.leg j).val := by
    simp only [stateCoefficient,PartialIsometry.target,mul_assoc]
  simp only [he]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,Q.total,hp,mul_one]
  simp only [stateCoefficient,mul_assoc]

/-- An actual finite sum of bounded vector functionals. -/
def matrixVectorFunctional (Q : EquivalentPartition p ι) (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  ∑ i, vectorFunctional ((Q.leg i).val.val ξ)

theorem matrixVectorFunctional_apply (Q : EquivalentPartition p ι) (ξ : H) (x : M.toStarSubalgebra) :
    Q.matrixVectorFunctional ξ x=∑ i, vectorFunctional ξ (Q.stateCoefficient x i i) := by
  change (∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x=_
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))=
    inner ℂ ξ (star (Q.leg i).val.val (x.val ((Q.leg i).val.val ξ)))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem matrixVectorFunctional_one (Q : EquivalentPartition p ι) (ξ : H) :
    Q.matrixVectorFunctional ξ 1=(∑ i, ‖(Q.leg i).val.val ξ‖^2 : ℝ) := by
  simp only [matrixVectorFunctional,sum_apply,vectorFunctional_apply]
  change (∑ i, inner ℂ ((Q.leg i).val.val ξ) ((Q.leg i).val.val ξ))=_
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_sum,Complex.ofReal_pow]
  norm_cast

theorem matrixVectorFunctional_norm_le (Q : EquivalentPartition p ι) (ξ : H) :
    ‖Q.matrixVectorFunctional ξ‖ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 := by
  change ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤ _
  calc ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤
      ∑ i, ‖vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ :=
        norm_sum_le Finset.univ (fun i : ι => vectorFunctional (M := M) ((Q.leg i).val.val ξ))
    _ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 :=
      Finset.sum_le_sum (fun i _ => vectorFunctional_norm_le (M := M) ((Q.leg i).val.val ξ))

theorem matrixVectorFunctional_nearly_cyclic (Q : EquivalentPartition p ι) (hp : p.val=1)
    (ξ : H) (ε : ℝ)
    (hcorner : ∀ x : M.toStarSubalgebra, Q.base.val*x=x → x*Q.base.val=x →
      (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re)
    (x : M.toStarSubalgebra) :
    (Q.matrixVectorFunctional ξ (star x*x)).re ≤
      (1+ε)*(Q.matrixVectorFunctional ξ (x*star x)).re := by
  have hl : (Q.matrixVectorFunctional ξ (star x*x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (star (Q.stateCoefficient x j i)*Q.stateCoefficient x j i)).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Q.stateCoefficient_star]
  have hr : (Q.matrixVectorFunctional ξ (x*star x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (Q.stateCoefficient x j i*star (Q.stateCoefficient x j i))).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    simp_rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_star]
  rw [hl,hr,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hcorner (Q.stateCoefficient x j i)
    (Q.stateCoefficient_left x j i) (Q.stateCoefficient_right x j i))

end EquivalentPartition
end

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance approxTraceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approxTraceOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approxTraceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance approxTraceStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- A constructed approximate tracial state on the entire original algebra. -/
theorem exists_approximately_tracial_state
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (ε : ℝ) (hε : 0<ε) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re ≤ (1+ε)*(φ (x*star x)).re := by
  classical
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,hE,hfaith,hcorner⟩ := exists_corner_nearly_cyclic_vector
    hfactor hdiff hfinite hunit ξ hξ ε hε
  obtain ⟨n,hn,Q,hQE,hQ⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  have hbase : 0<(vectorFunctional ξ Q.base.val).re := hfaith Q.base hQE hQ
  let A : ℝ := ∑ i, ‖(Q.leg i).val.val ξ‖^2
  have hi (i : Fin n) : ‖(Q.leg i).val.val ξ‖^2=(vectorFunctional ξ Q.base.val).re := by
    have h := congrArg Complex.re (vectorFunctional_star_mul_self ξ (Q.leg i).val)
    rw [(Q.leg i).initial,Q.initial] at h
    exact_mod_cast h.symm
  have hA : 0<A := by
    apply Finset.sum_pos
    · intro i _
      rw [hi]
      exact hbase
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  let F := Q.matrixVectorFunctional ξ
  have hF1 : F 1=(A : ℂ) := Q.matrixVectorFunctional_one ξ
  have hFnorm : ‖F‖ ≤ A := Q.matrixVectorFunctional_norm_le ξ
  have hFpos (x : M.toStarSubalgebra) (hx : 0 ≤ x) : 0 ≤ (F x).re := by
    change 0 ≤ ((∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x).re
    rw [sum_apply,Complex.re_sum]
    exact Finset.sum_nonneg (fun i _ => vectorFunctional_positive _ x hx)
  have hFtrace (x : M.toStarSubalgebra) : (F (star x*x)).re ≤ (1+ε)*(F (x*star x)).re := by
    apply Q.matrixVectorFunctional_nearly_cyclic rfl ξ ε ?_ x
    intro y hly hry
    have hl : E.val*y=y := by
      calc E.val*y = E.val*(Q.base.val*y) := by rw [hly]
           _ = y := by rw [← mul_assoc,show E.val*Q.base.val=Q.base.val from hQE,hly]
    have hr : y*E.val=y := by
      calc y*E.val = (y*Q.base.val)*E.val := by rw [hry]
           _ = y := by rw [mul_assoc,projection_mul_of_le hQE,hry]
    exact hcorner y hl hr
  let φ : M.toStarSubalgebra →L[ℂ] ℂ := ((A⁻¹ : ℝ) : ℂ) • F
  have hφ (x : M.toStarSubalgebra) : (φ x).re=A⁻¹*(F x).re := by
    simp only [φ,smul_apply,smul_eq_mul,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨φ,?_,?_,?_,?_⟩
  · change ‖((A⁻¹ : ℝ) : ℂ) • F‖ ≤ 1
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr hA.le)]
    exact (mul_le_mul_of_nonneg_left hFnorm (inv_nonneg.mpr hA.le)).trans_eq (inv_mul_cancel₀ hA.ne')
  · change ((A⁻¹ : ℝ) : ℂ)*(F 1)=1
    rw [hF1,← Complex.ofReal_mul,inv_mul_cancel₀ hA.ne',Complex.ofReal_one]
  · intro x hx
    rw [hφ]
    exact mul_nonneg (inv_nonneg.mpr hA.le) (hFpos x hx)
  · intro x
    rw [hφ,hφ]
    have h := mul_le_mul_of_nonneg_left (hFtrace x) (inv_nonneg.mpr hA.le)
    calc A⁻¹*(F (star x*x)).re ≤ A⁻¹*((1+ε)*(F (x*star x)).re) := h
         _ = (1+ε)*(A⁻¹*(F (x*star x)).re) := by ring

end Generator.Tracial

end

end OAI
