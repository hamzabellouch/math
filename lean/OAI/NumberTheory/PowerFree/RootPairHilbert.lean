import OAI.NumberTheory.PowerFree.ProjectionDegrees

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

theorem norm_projection_bounded {n d h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (k : ℕ) (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
    (θ : Fin d → K)
    (ha : ∀ i, Ideal.Quotient.mk I (a i) ≠ 0)
    (hab : ∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
      Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i))
    (hgen : Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
      Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤)
    (hx : Transcendental K (Ideal.Quotient.mk I x))
    (hdim : affineDimension I = h+1) (hd : h+1 ≤ d)
    (E D : ℕ) (hD : 0 < D) (hdeg : affineDegree I ≤ E)
    (hadeg : ∀ i, (a i).totalDegree ≤ D) (hxdeg : x.totalDegree ≤ D) :
    ∃ j : Fin (h+1) → Fin d, Function.Injective j ∧
      ∃ p : MvPolynomial (Option (Fin (h+1))) K, Irreducible p ∧
        p.totalDegree ≤ E*D^(h+1) ∧
        (∀ q, Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q) := by
  have htr : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = (h+1 : ℕ) := by
    rw [←hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)]
    change (affineDimension I : Cardinal) = _
    rw [hdim]
  have htd : Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) ≤ d := by
    rw [htr]
    exact_mod_cast hd
  obtain ⟨m,j,hj,hm,p,hp,hkp⟩ := pair_principal_projection_selection k
    (fun i => Ideal.Quotient.mk I (a i)) (fun i => Ideal.Quotient.mk I (b i))
    (Ideal.Quotient.mk I x) θ ha hab hgen hx htd
  have hmh : m = h := by
    have hh : m+1 = h+1 := by exact_mod_cast (hm.symm.trans htr)
    omega
  subst m
  have hker (q) : Ideal.Quotient.mk I (MvPolynomial.aeval (fun o => o.elim x (a ∘ j)) q) = 0 ↔ p ∣ q := by
    rw [←hkp]
    have hv : (fun o : Option (Fin (h+1)) => Ideal.Quotient.mk I (o.elim x (a ∘ j))) =
        (fun o => o.elim (Ideal.Quotient.mk I x) ((fun i => Ideal.Quotient.mk I (a i)) ∘ j)) := by
      funext o
      cases o <;> rfl
    change (Ideal.Quotient.mkₐ K I) (MvPolynomial.aeval _ q) = 0 ↔ _
    rw [MvPolynomial.comp_aeval_apply]
    change MvPolynomial.aeval (fun o : Option (Fin (h+1)) => Ideal.Quotient.mk I (o.elim x (a ∘ j))) q = 0 ↔ _
    rw [hv]
  refine ⟨j,hj,p,hp,?_,hker⟩
  have hb := affine_polynomial_projection_degree_bound (finSuccEquiv (h+1)) I hdim
    (fun o => o.elim x (a ∘ j)) D hD (by intro o; cases o with
      | none => exact hxdeg
      | some i => exact hadeg (j i)) p hp.ne_zero hker
  have hb' : (p.totalDegree:ℚ) ≤ (E:ℚ)*(D:ℚ)^(h+1) :=
    hb.trans (mul_le_mul_of_nonneg_right hdeg (by positivity))
  exact_mod_cast hb'

noncomputable def rootPairEvaluation {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) :
    RootPair k θ →ₐ[K] S :=
  pairEvaluation k (rootPairQ θ) (Polynomial.aeval x) a b (by
    intro i
    simpa only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C] using hab i)

@[simp] theorem rootPairEvaluation_left {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) (i : Fin d) :
    rootPairEvaluation k θ a b x hab (pairLeft k (rootPairQ θ) i) = a i := by
  simp [rootPairEvaluation]

@[simp] theorem rootPairEvaluation_right {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) (i : Fin d) :
    rootPairEvaluation k θ a b x hab (pairRight k (rootPairQ θ) i) = b i := by
  simp [rootPairEvaluation]

@[simp] theorem rootPairEvaluation_number {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) :
    rootPairEvaluation k θ a b x hab (pairCoeffMap k (rootPairQ θ) Polynomial.X) = x := by
  simp [rootPairEvaluation]

theorem rootPairEvaluation_projection {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i))
    (p : MvPolynomial (Option (Fin d)) K) :
    rootPairEvaluation k θ a b x hab
      (positiveToPair k (rootPairQ θ) (optionEquivRight K (Fin d) p)) =
      MvPolynomial.aeval (fun o => o.elim x a) p := by
  rw [positiveToPair_option,MvPolynomial.comp_aeval_apply]
  congr 1
  congr 1
  funext o
  cases o with
  | none => exact rootPairEvaluation_number k θ a b x hab
  | some i => exact rootPairEvaluation_left k θ a b x hab i

theorem rootPairEvaluation_comp_kernel {d : ℕ} {K S L : Type*}
    [Field K] [CommRing S] [CommRing L] [Algebra K S] [Algebra K L]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i))
    (e : S →ₐ[K] L) (he : Function.Injective e)
    (p : MvPolynomial (Option (Fin d)) K)
    (hker : ∀ q, MvPolynomial.aeval (fun o => o.elim x a) q = 0 ↔ p ∣ q) :
    ∀ q, (e.comp (rootPairEvaluation k θ a b x hab))
      (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin d) p ∣ q := by
  intro q
  let E := MvPolynomial.optionEquivRight K (Fin d)
  let q₀ := E.symm q
  have heq : E q₀ = q := E.apply_symm_apply q
  rw [←heq,AlgHom.comp_apply,rootPairEvaluation_projection,map_eq_zero_iff e he,hker]
  exact (map_dvd_iff E).symm

end
section
universe u v
open scoped BigOperators
theorem rootPair_actual_hilbert_uniform_allFields {n : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (E : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type v) [Field L] [Algebra K L], ∀ (θ : Fin (n+1) → K), Function.Injective θ →
      ∀ (ψ : RootPair k θ →ₐ[K] L), (∀ i, ψ (pairLeft k (rootPairQ θ) i) ≠ 0) →
      ∀ (p : MvPolynomial (Option (Fin (n+1))) K), p ≠ 0 → p.totalDegree ≤ E →
      (∀ q, ψ (positiveToPair k (rootPairQ θ) q) = 0 ↔
        MvPolynomial.optionEquivRight K (Fin (n+1)) p ∣ q) →
      ∃ u v : ℕ, min A B ≤ A*u+B*v ∧ A*u+B*v ≤ (k*A+B)*E ∧
        ∀ T : ℕ, (k*A+B)*E ≤ T →
        |(Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
          (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) : ℝ) -
          ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^n /
            (((n+1).factorial:ℝ)*(A:ℝ)^(n+1)*(B:ℝ)^(n+1))*(T:ℝ)^(n+1)| ≤
          C*((T:ℝ)+1)^n := by
  classical
  let M := (k*A+B)*E
  choose C hC0 hC using fun u v =>
    pairAffine_cut_hilbert_uniform (n := n) (K := K) k A B hA hB u v
  let Ctotal : ℝ := ∑ u ∈ Finset.range (M+1), ∑ v ∈ Finset.range (M+1), C u v
  have htotal : 0 ≤ Ctotal := Finset.sum_nonneg fun u _ =>
    Finset.sum_nonneg fun v _ => hC0 u v
  refine ⟨Ctotal,htotal,fun L _ _ θ hθ ψ ha p hp hpE hker => ?_⟩
  obtain ⟨u,v,c,hD,hc,hc0,hct,hkerφ⟩ := rootPair_bounded_cone_kernel hk A B hB θ hθ ψ ha p hp hker
  let φ := ψ.comp (pairConeToRoot k A B θ)
  have hφc : φ c = 0 := by
    apply (show c ∈ RingHom.ker φ.toRingHom ↔ φ c = 0 from Iff.rfl).mp
    rw [hkerφ]
    exact (show Ideal.span {c} ≤ _ from le_sup_left) (Ideal.subset_span (Set.mem_singleton _))
  have hDpos : A*u+B*v ≠ 0 := by
    intro hh
    have hu := (pairCone_degree_zero_isUnit k A B hA hB (coneDifference θ) c hc0 (hh ▸ hc)).map φ
    exact hu.ne_zero hφc
  have hDlower : min A B ≤ A*u+B*v := by
    by_cases hu : u = 0
    · have hv : 1 ≤ v := by
        by_contra hh
        have hv0 : v = 0 := by omega
        exact hDpos (by simp [hu,hv0])
      exact (min_le_right A B).trans ((show B ≤ B*v by simpa using Nat.mul_le_mul_left B hv).trans (Nat.le_add_left _ _))
    · exact (min_le_left A B).trans ((show A ≤ A*u by simpa using Nat.mul_le_mul_left A (Nat.one_le_iff_ne_zero.mpr hu)).trans (Nat.le_add_right _ _))
  have hbound : A*u+B*v ≤ M := hD.trans (Nat.mul_le_mul_left _ hpE)
  have hu : u ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right u hA)
    (Nat.le_add_right (A*u) (B*v))) hbound
  have hv : v ≤ M := le_trans (le_trans (by simpa using Nat.mul_le_mul_right v hB)
    (Nat.le_add_left (B*v) (A*u))) hbound
  have hsum : C u v ≤ Ctotal := by
    calc C u v ≤ ∑ j ∈ Finset.range (M+1), C u j :=
          Finset.single_le_sum (fun j _ => hC0 u j) (Finset.mem_range.mpr (by omega))
      _ ≤ Ctotal := Finset.single_le_sum (fun i _ =>
          Finset.sum_nonneg (fun j _ => hC0 i j)) (Finset.mem_range.mpr (by omega))
  refine ⟨u,v,hDlower,hbound,fun T hT => ?_⟩
  have hh := hC u v (coneDifference θ) c hc0 hc hct T (hbound.trans hT)
  rw [finrank_map_quotient_kernel φ _ hkerφ] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

end
section
open MvPolynomial
open scoped BigOperators

theorem pairCone_homogeneous_image_le {n : ℕ} {σ K S : Type*}
    [Fintype σ] [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K)
    (φ : PairCone k A B θ →ₐ[K] S) (g : MvPolynomial σ K →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) = 1)
    (a b : Fin (n+1) → MvPolynomial σ K) (w : σ → ℕ)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hφa : ∀ i, φ (pairConeA k A B θ i) = g (a i))
    (hφb : ∀ i, φ (pairConeB k A B θ i) = g (b i)) (T : ℕ) :
    (homogeneousSpace (pairConeScale k A B θ) T).map φ.toLinearMap ≤
      (weightedSpace w T).map g.toLinearMap := by
  classical
  rintro y ⟨c,hc,rfl⟩
  let p := pairConePolynomial k A B hB θ c
  let z := Sum.elim a b
  let v : Fin (n+1) ⊕ Fin (n+1) → ℕ := Sum.elim (fun _ => A) (fun _ => B)
  have hp : p ∈ weightedSpace v T := by
    intro m hm
    have hh := pairConePolynomial_weight k A B hB θ c T
      ((mem_homogeneousSpace _ _ _).mp hc) m hm
    have he : Finsupp.weight v m = A*(∑ i, m (Sum.inl i))+ B*(∑ i, m (Sum.inr i)) := by
      rw [Finsupp.weight_eq_sum,Fintype.sum_sum_type]
      simp only [v,Sum.elim_inl,Sum.elim_inr,nsmul_eq_mul,Nat.cast_id,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    change Finsupp.weight v m ≤ T
    rwa [he]
  have hz : ∀ i, z i ∈ weightedSpace w (v i) := by
    intro i
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  refine ⟨MvPolynomial.aeval z p,weightedSpace_aeval v w z hz p T hp,?_⟩
  change g (MvPolynomial.aeval z p) = φ c
  rw [MvPolynomial.comp_aeval_apply]
  have hv : g ∘ z = Sum.elim (φ ∘ pairConeA k A B θ) (φ ∘ pairConeB k A B θ) := by
    funext i
    cases i with
    | inl i => exact (hφa i).symm
    | inr i => exact (hφb i).symm
  change MvPolynomial.aeval (g ∘ z) p = φ c
  rw [hv]
  exact pairConePolynomial_eval k A B hB θ φ ht c

theorem rootPair_actual_hilbert_le {n N : ℕ} {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial (Fin N) K))
    (e : (MvPolynomial (Fin N) K ⧸ I) →ₐ[K] L) (he : Function.Injective e)
    (k A B : ℕ) (hB : 0 < B) (θ : Fin (n+1) → K)
    (ψ : RootPair k θ →ₐ[K] L)
    (a b : Fin (n+1) → MvPolynomial (Fin N) K) (w : Fin N → ℕ)
    (hw : ∀ i, w i ≠ 0)
    (ha : ∀ i, a i ∈ weightedSpace w A) (hb : ∀ i, b i ∈ weightedSpace w B)
    (hψa : ∀ i, ψ (pairLeft k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (a i)))
    (hψb : ∀ i, ψ (pairRight k (rootPairQ θ) i) = e (Ideal.Quotient.mk I (b i))) (T : ℕ) :
    Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference θ)) T).map
      (ψ.comp (pairConeToRoot k A B θ)).toLinearMap) ≤
    Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let g := e.comp (Ideal.Quotient.mkₐ K I)
  have := weightedSpace_finite (K := K) w hw T
  have hh := pairCone_homogeneous_image_le k A B hB (coneDifference θ)
    (ψ.comp (pairConeToRoot k A B θ)) g (by simp) a b w ha hb
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_left] using hψa i)
    (fun i => by simpa only [g,AlgHom.comp_apply,Ideal.Quotient.mkₐ_eq_mk,pairConeToRoot_right] using hψb i) T
  have hr : Module.finrank K ((weightedSpace w T).map g.toLinearMap) =
      Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
    apply finrank_map_eq_of_kernel_eq
    ext p
    change e (Ideal.Quotient.mk I p) = 0 ↔ Ideal.Quotient.mk I p = 0
    exact map_eq_zero_iff e he
  exact (Submodule.finrank_mono hh).trans_eq hr

end
open MvPolynomial

universe u

theorem norm_ambient_hilbert_uniform {n d h : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) →
      affineDimension I = h+1 → h+1 ≤ d → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ T : ℕ, (k*A+B)*(E*D^(h+1)) ≤ T →
        ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) -
          C*((T:ℝ)+1)^h ≤
          (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by
  obtain ⟨C,hC,hunif⟩ := rootPair_actual_hilbert_uniform_allFields.{u,u}
    (n := h) (K := K) hk A B hA hB (E*D^(h+1))
  refine ⟨C,hC,fun I _ a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw T hT => ?_⟩
  obtain ⟨j,hj,p,hp,hpD,hkp⟩ := norm_projection_bounded I k a b x θ ha hab hgen hx
    hdim hd E D hD hdeg hadeg hxdeg
  let S := MvPolynomial (Fin n) K ⧸ I
  let L := FractionRing S
  let e : S →ₐ[K] L := IsScalarTower.toAlgHom K S L
  have he : Function.Injective e := IsFractionRing.injective S L
  let aj : Fin (h+1) → S := fun i => Ideal.Quotient.mk I (a (j i))
  let bj : Fin (h+1) → S := fun i => Ideal.Quotient.mk I (b (j i))
  let xj : S := Ideal.Quotient.mk I x
  have habj : ∀ i, aj i ^ k * bj i = xj - algebraMap K S ((θ ∘ j) i) := fun i => hab (j i)
  let ψ : RootPair k (θ ∘ j) →ₐ[K] L := e.comp (rootPairEvaluation k (θ ∘ j) aj bj xj habj)
  have hψa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (a (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_left,aj]
  have hψb (i) : ψ (pairRight k (rootPairQ (θ ∘ j)) i) = e (Ideal.Quotient.mk I (b (j i))) := by
    simp only [ψ,AlgHom.comp_apply,rootPairEvaluation_right,bj]
  have hpa (i) : ψ (pairLeft k (rootPairQ (θ ∘ j)) i) ≠ 0 := by
    rw [hψa,map_ne_zero_iff e he]
    exact ha (j i)
  have hproj (q) : MvPolynomial.aeval (fun o => o.elim xj aj) q = 0 ↔ p ∣ q := by
    rw [←hkp]
    have hh := MvPolynomial.comp_aeval_apply
      (f := fun o : Option (Fin (h+1)) => o.elim x (a ∘ j)) (Ideal.Quotient.mkₐ K I) q
    have hv : (fun o : Option (Fin (h+1)) => (Ideal.Quotient.mkₐ K I) (o.elim x (a ∘ j))) =
        (fun o => o.elim xj aj) := by funext o; cases o <;> rfl
    rw [hv] at hh
    exact Iff.of_eq (congrArg (fun y => y = 0) hh.symm)
  have hker := rootPairEvaluation_comp_kernel k (θ ∘ j) aj bj xj habj e he p hproj
  obtain ⟨r,s,hmin,_,hH⟩ := hunif L (θ ∘ j) (hθ.comp hj) ψ hpa p hp.ne_zero hpD hker
  have hR := rootPair_actual_hilbert_le I e he k A B hB (θ ∘ j) ψ
    (a ∘ j) (b ∘ j) w hw (fun i => haw (j i)) (fun i => hbw (j i)) hψa hψb T
  have hH' := (abs_le.mp (hH T hT)).1
  have hcoef : ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
      (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) ≤
    ((A*r+B*s : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
      (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1) := by
    gcongr
  have hR' : (Module.finrank K ((homogeneousSpace (pairConeScale k A B (coneDifference (θ ∘ j))) T).map
      (ψ.comp (pairConeToRoot k A B (θ ∘ j))).toLinearMap) : ℝ) ≤
      (Module.finrank K ((weightedSpace w T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℝ) := by exact_mod_cast hR
  linarith

end QuarticPowerFree

end OAI
