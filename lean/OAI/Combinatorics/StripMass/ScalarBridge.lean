import Mathlib
import OAI.Combinatorics.StripMass.PairCoordinates
import OAI.Combinatorics.StripMass.ArchRoots

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

 

theorem pfaffian_eq_exterior (m : ℕ) (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian A = StripPfaffian.pfaffian (m*2) A := by
  rw [StripPfaffian.pfaffian_permutation_expansion m A hA]
  unfold pfaffian
  simp only [Nat.mul_div_cancel m (by omega : 0<2)]
  have hc : ((2:ℂ)^m * (m.factorial:ℂ))⁻¹ = (1/2:ℂ)^m / m.factorial := by
    simp [mul_inv_rev, div_eq_mul_inv, mul_comm]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  unfold StripPfaffian.pairEntries
  apply Fintype.prod_equiv (finCongr (Nat.mul_div_cancel m (by norm_num : 0 < 2)))
  intro i
  congr 2 <;> apply Fin.ext <;>
    simp [pairFirst,pairSecond,StripPfaffian.pairLeft,StripPfaffian.pairRight,
      finProdFinEquiv,mul_comm,add_comm]

lemma augmentedKernel_skew_complex {n : ℕ} (a : Fin n → ℂ) :
    ∀ i j, augmentedKernel (d:ℂ) (rho:ℂ) a j i =
      -augmentedKernel (d:ℂ) (rho:ℂ) a i j := by
  intro i j
  by_cases hi : i.val<n <;> by_cases hj : j.val<n
  all_goals simp only [augmentedKernel,hi,hj,↓reduceDIte,↓reduceIte]
  · have hd : discriminant (d:ℂ) (a ⟨j.val,hj⟩) (a ⟨i.val,hi⟩) =
        discriminant (d:ℂ) (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩) := by
      unfold discriminant; ring
    rw [hd,←neg_div]
    congr 1
    ring
  all_goals ring

lemma scalarNormalization_eq_exterior {n : ℕ} (a : Fin n → ℂ) :
    scalarNormalization (d:ℂ) (rho:ℂ) a=StripPfaffian.p n a := by
  have he : n+n%2=((n+1)/2)*2 := by omega
  unfold scalarNormalization StripPfaffian.p
  congr 1
  let A := augmentedKernel (d:ℂ) (rho:ℂ) a
  let A' : Matrix (Fin (((n+1)/2)*2)) (Fin (((n+1)/2)*2)) ℂ :=
    fun i j =>A (i.cast he.symm) (j.cast he.symm)
  calc
    pfaffian A = pfaffian A' := (pfaffian_cast he A).symm
    _ = StripPfaffian.pfaffian (((n+1)/2)*2) A' :=
      pfaffian_eq_exterior _ _ (fun i j =>augmentedKernel_skew_complex a _ _)
    _ = StripPfaffian.pfaffian (StripPfaffian.pfSize n)
        (StripPfaffian.augmentedKernel n a) := by
      have he' : ((n+1)/2)*2=StripPfaffian.pfSize n := by
        unfold StripPfaffian.pfSize; omega
      have hcast {u v:ℕ} (h:u=v) (M:Matrix (Fin u) (Fin u) ℂ) :
          StripPfaffian.pfaffian v (fun i j=>M (i.cast h.symm) (j.cast h.symm)) =
            StripPfaffian.pfaffian u M := by subst v; rfl
      rw [←hcast he' A']
      congr 1

end

noncomputable section
open scoped Classical BigOperators
open Filter Topology

lemma scalarValue_eq_exterior {n : ℕ} (a : Fin n → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → StripPfaffian.D (a i) (a j) ≠ 0) :
    scalarValue (RingHom.id ℂ) a=StripPfaffian.p n a := by
  have hD' : ∀ i j, i≠j → discriminant ((RingHom.id ℂ) (d:ℂ)) (a i) (a j)≠0 := hD
  rw [scalarValue, scalarPolynomial_eval (RingHom.id ℂ) n (d:ℂ) (rho:ℂ) _ a ha hD']
  exact scalarNormalization_eq_exterior a

 

def archPolynomialAt {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.C (scalarValue (RingHom.id ℂ) a)⁻¹ * nextScalar (RingHom.id ℂ) a

lemma archPolynomialAt_monic_degree {n : ℕ} (a : Fin n → ℂ)
    (hp : scalarValue (RingHom.id ℂ) a≠0) :
    (archPolynomialAt a).Monic ∧ (archPolynomialAt a).natDegree=n := by
  have hd : (archPolynomialAt a).natDegree≤n :=
    (Polynomial.natDegree_C_mul_le _ _).trans (nextScalar_degree _ _)
  have hc : (archPolynomialAt a).coeff n=1 := by
    simp [archPolynomialAt,nextScalar_top,hp]
  have he : (archPolynomialAt a).natDegree=n :=
    le_antisymm hd (Polynomial.le_natDegree_of_ne_zero (hc ▸ one_ne_zero))
  exact ⟨by rw [Polynomial.Monic,Polynomial.leadingCoeff,he,hc],he⟩

lemma nextScalar_eval {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (nextScalar (RingHom.id ℂ) a).eval z = scalarValue (RingHom.id ℂ) (Fin.snoc a z) := by
  rw [scalarValue_snoc]
  exact eval_firstScalarHom _ _ _ _

lemma archPolynomialAt_eval_quotient {n : ℕ} (a : Fin n → ℂ)
    (ha : Function.Injective a)
    (hD : ∀ i j, i≠j → StripPfaffian.D (a i) (a j)≠0) (z : ℂ)
    (hz : ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0) :
    (archPolynomialAt a).eval z = StripPfaffian.p (n+1) (Fin.snoc a z) / StripPfaffian.p n a := by
  have hi : Function.Injective (Fin.snoc a z) :=
    Fin.snoc_injective_of_injective ha (by rintro ⟨i,hi⟩; exact (hz i).1 hi.symm)
  have hs : ∀ i j : Fin (n+1), i≠j → StripPfaffian.D ((Fin.snoc a z : Fin (n+1) → ℂ) i) ((Fin.snoc a z : Fin (n+1) → ℂ) j)≠0 := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j =>
        simpa [StripPfaffian.D,add_comm,add_left_comm,mul_comm,mul_left_comm] using (hz j).2
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa using (hz i).2
      | cast j => simpa using hD i j (fun he => hij (congrArg Fin.castSucc he))
  rw [archPolynomialAt,Polynomial.eval_mul,Polynomial.eval_C,nextScalar_eval,
    scalarValue_eq_exterior a ha hD,scalarValue_eq_exterior _ hi hs,div_eq_mul_inv,mul_comm]

lemma infinitely_many_regular_arguments {n : ℕ} (a : Fin n → ℂ) :
    Set.Infinite {z : ℂ | ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0} := by
  let bad : Set ℂ := Set.range a ∪ ⋃ i, {z : ℂ | (StripPfaffian.Dpoly (a i)).IsRoot z}
  have hb : bad.Finite := (Set.finite_range a).union (Set.finite_iUnion (fun i =>
    Polynomial.finite_setOfPred_isRoot (by
      intro he
      have hh := StripPfaffian.Dpoly_coeff (a i)
      rw [he,Polynomial.coeff_zero] at hh
      exact zero_ne_one hh)))
  have h : badᶜ = {z : ℂ | ∀ i, z≠a i ∧ StripPfaffian.D (a i) z≠0} := by
    ext z
    simp only [bad,Set.mem_compl_iff,Set.mem_union,Set.mem_range,Set.mem_iUnion,
      Set.mem_ofPred_eq,not_or,not_exists,Polynomial.IsRoot,StripPfaffian.Dpoly_eval]
    exact ⟨fun h i => ⟨Ne.symm (h.1 i),h.2 i⟩,fun h => ⟨fun i => (h i).1.symm,fun i => (h i).2⟩⟩
  rw [←h]
  exact hb.infinite_compl

 

theorem archPolynomialAt_confluent (n : ℕ) (hn : 1≤n) :
    ∃ g₀ : Polynomial ℝ, MonicProblem n g₀ ∧
      (∀ q, MonicProblem n q → q=g₀) ∧
      ∃ g : (Fin n → ℂ) → Polynomial ℂ,
        g (fun _ => (C:ℂ))=g₀.map Complex.ofRealHom ∧
        (∀ k, ContinuousAt (fun a => (g a).coeff k) (fun _ => (C:ℂ))) ∧
        ∀ᶠ a in 𝓝 (fun _ : Fin n => (C:ℂ)),
          (g a).Monic ∧ (g a).natDegree=n ∧
            ∀ (_ha : Function.Injective a)
            (_hD : ∀ i j, i≠j → StripPfaffian.D (a i) (a j)≠0)
            (_hp : scalarValue (RingHom.id ℂ) a≠0),
              archPolynomialAt a=g a := by
  obtain ⟨g₀,hg₀,hu,g,hg,hgc,hgreg⟩ := StripPfaffian.pfaffian_confluent_limit n hn
  refine ⟨g₀,hg₀,hu,g,hg,hgc,?_⟩
  filter_upwards [hgreg] with a ha
  refine ⟨ha.1,ha.2.1,?_⟩
  intro hinj hD hp
  apply Polynomial.eq_of_infinite_eval_eq
  apply (infinitely_many_regular_arguments a).mono
  intro z hz
  have hpn : StripPfaffian.p n a≠0 := by rwa [←scalarValue_eq_exterior a hinj hD]
  exact (archPolynomialAt_eval_quotient a hinj hD z hz).trans (ha.2.2 hinj hD hpn z hz).symm

end
end CriticalStrip.Diagram
 

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical

 
def PathBetween (N : ℕ) (start finish : Triangle) (p : List Triangle) : Prop :=
  p.head?=some start ∧ p.getLast?=some finish ∧ p.Nodup ∧
    p.IsChain adjacent ∧ ∀ v ∈ p, v.2.1<N

@[simp] lemma pathBetween_source (N : ℕ) (finish : Triangle) (p : List Triangle) :
    PathBetween N (up 0 0) finish p ↔ IsPath N finish p := Iff.rfl

lemma adjacent_symmetric : Std.Symm adjacent := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩

lemma PathBetween.reverse {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) : PathBetween N b a p.reverse := by
  refine ⟨by simpa using hp.2.1,by simpa using hp.1,(by simpa only [List.nodup_reverse] using hp.2.2.1),?_,?_⟩
  · exact List.isChain_reverse.mpr (hp.2.2.2.1.imp (fun _ _ h => adjacent_symmetric.symm _ _ h))
  · intro v hv
    exact hp.2.2.2.2 v (List.mem_reverse.mp hv)

 
def translateTriangle (i : ℤ) (v : Triangle) : Triangle := (i+v.1,v.2)

@[simp] lemma translateTriangle_up (i j : ℤ) (k : ℕ) :
    translateTriangle i (up j k)=up (i+j) k := rfl
@[simp] lemma translateTriangle_down (i j : ℤ) (k : ℕ) :
    translateTriangle i (down j k)=down (i+j) k := rfl
@[simp] lemma translateTriangle_band (i : ℤ) (v : Triangle) :
    (translateTriangle i v).2.1=v.2.1 := rfl
@[simp] lemma translateTriangle_zero (v : Triangle) : translateTriangle 0 v=v := by
  cases v; simp [translateTriangle]
@[simp] lemma translateTriangle_add (i j : ℤ) (v : Triangle) :
    translateTriangle i (translateTriangle j v)=translateTriangle (i+j) v := by
  simp [translateTriangle,add_assoc]

lemma translateTriangle_injective (i : ℤ) : Function.Injective (translateTriangle i) := by
  intro v w h
  have := congrArg (translateTriangle (-i)) h
  simpa using this

lemma adjacent_translate_iff (i : ℤ) (v w : Triangle) :
    adjacent (translateTriangle i v) (translateTriangle i w) ↔ adjacent v w := by
  simp only [adjacent,upDownAdjacent,translateTriangle,add_assoc,add_left_cancel_iff]

lemma PathBetween.translate {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) := by
  refine ⟨?_,?_,hp.2.2.1.map (translateTriangle_injective i),?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · exact (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun _ _ => (adjacent_translate_iff i _ _).mpr))
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact hp.2.2.2.2 w hw

@[simp] lemma pathBetween_translate_iff (N : ℕ) (a b : Triangle) (p : List Triangle) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) ↔
      PathBetween N a b p := by
  refine ⟨fun h => ?_,fun h => h.translate i⟩
  simpa [List.map_map,Function.comp_def] using h.translate (-i)

def translatePaths (i : ℤ) : List Triangle ≃ List Triangle where
  toFun := List.map (translateTriangle i)
  invFun := List.map (translateTriangle (-i))
  left_inv := by intro p; simp [List.map_map,Function.comp_def]
  right_inv := by intro p; simp [List.map_map,Function.comp_def]

 
def betweenArchWeight (N : ℕ) (i j : ℤ) (p : List Triangle) : ℝ :=
  if i≠j ∧ PathBetween N (up i 0) (up j 0) p then rho^p.length else 0

def betweenArchKernel (N : ℕ) (i j : ℤ) : ℝ := ∑' p, betweenArchWeight N i j p

lemma betweenArchWeight_nonneg (N : ℕ) (i j : ℤ) (p : List Triangle) :
    0≤betweenArchWeight N i j p := by
  unfold betweenArchWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl

lemma betweenArchWeight_translate (N : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N i j (p.map (translateTriangle i))=archWeight N (j-i) p := by
  have hi : up i 0=translateTriangle i (up 0 0) := by simp
  have hj : up j 0=translateTriangle i (up (j-i) 0) := by simp
  have hn : i≠j ↔ j-i≠0 := by omega
  simp only [betweenArchWeight,archWeight,hi,hj,pathBetween_translate_iff,
    pathBetween_source,hn,List.length_map]

 

theorem betweenArchKernel_eq (N : ℕ) (i j : ℤ) : betweenArchKernel N i j=K N (j-i) := by
  rw [betweenArchKernel,←(translatePaths i).tsum_eq]
  exact tsum_congr (betweenArchWeight_translate N i j)

lemma summable_betweenArchWeight_iff (N : ℕ) (i j : ℤ) :
    Summable (betweenArchWeight N i j) ↔ Summable (archWeight N (j-i)) := by
  rw [←(translatePaths i).summable_iff]
  exact summable_congr (betweenArchWeight_translate N i j)

lemma betweenArchWeight_reverse (N : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N j i p.reverse=betweenArchWeight N i j p := by
  have hp : PathBetween N (up j 0) (up i 0) p.reverse ↔ PathBetween N (up i 0) (up j 0) p := by
    refine ⟨fun h => ?_,PathBetween.reverse⟩
    simpa using h.reverse
  simp only [betweenArchWeight,hp,ne_comm,List.length_reverse]

 

def cutArchWeight (N : ℕ) (x : (ℕ×ℕ)×List Triangle) : ℝ :=
  betweenArchWeight N (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2

lemma cutArchWeight_nonneg (N : ℕ) (x : (ℕ×ℕ)×List Triangle) : 0≤cutArchWeight N x :=
  betweenArchWeight_nonneg _ _ _ _

lemma cutArchWeight_path_sum (N : ℕ) (x : ℕ×ℕ) :
    (∑' p,cutArchWeight N (x,p))=K N ((x.1+x.2:ℕ)+1) := by
  change betweenArchKernel N (-(x.1:ℤ)) ((x.2:ℤ)+1)=_
  rw [betweenArchKernel_eq]
  congr 1
  omega

 

lemma summable_add_diagonal_iff {f : ℕ→ℝ} (hf : ∀ n,0≤f n) :
    Summable (fun x : ℕ×ℕ => f (x.1+x.2)) ↔ Summable (fun n : ℕ => (n+1:ℝ)*f n) := by
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  change Summable (fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
    f (x.2.val.1+x.2.val.2)) ↔ _
  rw [summable_sigma_of_nonneg (fun x => hf _)]
  have hsum (n : ℕ) : (∑' x : Finset.HasAntidiagonal.antidiagonal n,
      f (x.val.1+x.val.2))=(n+1:ℝ)*f n := by
    have he (x : Finset.HasAntidiagonal.antidiagonal n) : x.val.1+x.val.2=n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp x.property
    simp only [he,tsum_const,Nat.card_eq_fintype_card,nsmul_eq_mul,Fintype.card_coe,Finset.Nat.card_antidiagonal,
      Nat.cast_add,Nat.cast_one]
  simp only [hsum]
  exact ⟨fun h => h.2,fun h => ⟨fun _ => (hasSum_fintype _).summable,h⟩⟩

lemma tsum_add_diagonal {f : ℕ→ℝ} (hf : ∀ n,0≤f n)
    (h : Summable (fun n : ℕ => (n+1:ℝ)*f n)) :
    (∑' x : ℕ×ℕ,f (x.1+x.2))=∑' n : ℕ,(n+1:ℝ)*f n := by
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff).mpr
    ((summable_add_diagonal_iff hf).mpr h)
  change Summable (fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
    f (x.2.val.1+x.2.val.2)) at hs
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  change (∑' x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n,
    f (x.2.val.1+x.2.val.2)) = _
  rw [hs.tsum_sigma' (fun _=>(hasSum_fintype _).summable)]
  apply tsum_congr
  intro n
  have he (x : Finset.HasAntidiagonal.antidiagonal n) : x.val.1+x.val.2=n :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp x.property
  simp only [he,tsum_const,Nat.card_eq_fintype_card,nsmul_eq_mul,Fintype.card_coe,Finset.Nat.card_antidiagonal,
    Nat.cast_add,Nat.cast_one]

 

theorem cutArchWeight_summable_iff (N : ℕ)
    (hK : ∀ k : ℤ,Summable (archWeight N k)) :
    Summable (cutArchWeight N) ↔ Summable (fun n : ℕ => (n+1:ℝ)*K N (n+1)) := by
  rw [summable_prod_of_nonneg (cutArchWeight_nonneg N)]
  have hi (x : ℕ×ℕ) : Summable (fun p => cutArchWeight N (x,p)) :=
    (summable_betweenArchWeight_iff N (-(x.1:ℤ)) ((x.2:ℤ)+1)).mpr (hK _)
  have he (x : ℕ×ℕ) : (∑' p, cutArchWeight N (x,p)) =
      (fun n : ℕ => K N (n+1)) (x.1+x.2) := cutArchWeight_path_sum N x
  have hh : Summable (fun x : ℕ×ℕ => ∑' p,cutArchWeight N (x,p)) ↔
      Summable (fun x : ℕ×ℕ => (fun n : ℕ => K N (n+1)) (x.1+x.2)) := summable_congr he
  exact ⟨fun h => (summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mp (hh.mp h.2),
    fun h => ⟨hi,hh.mpr ((summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mpr h)⟩⟩

 

theorem physical_moment_eq_cut_sum {N : ℕ} (hN : StripSumsFinite N) :
    moment N=∑' x,cutArchWeight N x := by
  have hs := (cutArchWeight_summable_iff N hN.1).mpr hN.2.2.2.2
  rw [hs.tsum_prod]
  simp only [cutArchWeight_path_sum]
  exact (tsum_add_diagonal (fun n => K_nonneg N (n+1)) hN.2.2.2.2).symm

end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology

 
def steppedDomain (N : ℕ) (s : ℤ) (v : Triangle) : Prop :=
  v.2.1 < N ∨ v.2.1=N ∧ s ≤ v.1

 

def stepArchWeight (N : ℕ) (s i j : ℤ) (p : List Triangle) : ℝ :=
  if ∀ v∈p,steppedDomain N s v then betweenArchWeight (N+1) i j p else 0

def stepArchKernel (N : ℕ) (s i j : ℤ) : ℝ := ∑' p, stepArchWeight N s i j p

lemma stepArchWeight_nonneg (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    0 ≤ stepArchWeight N s i j p := by
  unfold stepArchWeight
  split
  · exact betweenArchWeight_nonneg _ _ _ _
  · exact le_rfl

lemma stepArchWeight_le (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    stepArchWeight N s i j p ≤ betweenArchWeight (N+1) i j p := by
  unfold stepArchWeight
  split
  · exact le_rfl
  · exact betweenArchWeight_nonneg _ _ _ _

lemma stepArchWeight_reverse (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    stepArchWeight N s j i p.reverse=stepArchWeight N s i j p := by
  simp only [stepArchWeight,List.mem_reverse,betweenArchWeight_reverse]

def reversePaths : List Triangle ≃ List Triangle where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

lemma stepArchKernel_reverse (N : ℕ) (s i j : ℤ) :
    stepArchKernel N s j i=stepArchKernel N s i j := by
  rw [stepArchKernel,←reversePaths.tsum_eq]
  exact tsum_congr (stepArchWeight_reverse N s i j)

lemma betweenArchWeight_mono {N M : ℕ} (hNM : N ≤ M) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N i j p ≤ betweenArchWeight M i j p := by
  unfold betweenArchWeight
  split_ifs with hn hm hm
  · exact le_rfl
  · exact (hm ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,
      fun v hv => (hn.2.2.2.2.2 v hv).trans_le hNM⟩).elim
  · exact (pow_pos rho_pos _).le
  · exact le_rfl

lemma betweenArchWeight_restrict (N : ℕ) (i j : ℤ) (p : List Triangle) :
    (if ∀ v∈p,v.2.1 < N then betweenArchWeight (N+1) i j p else 0)=betweenArchWeight N i j p := by
  by_cases h : ∀ v∈p,v.2.1 < N
  · have hpath : PathBetween (N+1) (up i 0) (up j 0) p ↔
        PathBetween N (up i 0) (up j 0) p := by
      constructor
      · intro hp; exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,h⟩
      · intro hp; exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,fun v hv => (h v hv).trans_le (Nat.le_succ _)⟩
    simp only [ite_eq_left h,betweenArchWeight,hpath]
  · rw [ite_eq_right h,betweenArchWeight,ite_eq_right]
    rintro ⟨_,hp⟩
    exact h hp.2.2.2.2

lemma stepArchWeight_translate (N : ℕ) (s i j q : ℤ) (p : List Triangle) :
    stepArchWeight N s (q+i) (q+j) (p.map (translateTriangle q)) =
      stepArchWeight N (s-q) i j p := by
  have hb : betweenArchWeight (N+1) (q+i) (q+j) (p.map (translateTriangle q))=
      betweenArchWeight (N+1) i j p := by
    simp only [betweenArchWeight,←translateTriangle_up,pathBetween_translate_iff,List.length_map,
      ne_eq,add_left_cancel_iff]
  have he : (∀ v∈p.map (translateTriangle q),steppedDomain N s v) ↔
      ∀ v∈p,steppedDomain N (s-q) v := by
    simp only [List.forall_mem_map,steppedDomain,translateTriangle]
    exact forall_congr' (fun v => forall_congr' (fun _ => by omega))
  simp only [stepArchWeight,he,hb]

 
def stepCutArchWeight (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) : ℝ :=
  stepArchWeight N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2

lemma stepCutArchWeight_nonneg (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) :
    0 ≤ stepCutArchWeight N s x := stepArchWeight_nonneg _ _ _ _ _

lemma stepCutArchWeight_le (N : ℕ) (s : ℤ) (x : (ℕ×ℕ)×List Triangle) :
    stepCutArchWeight N s x ≤ cutArchWeight (N+1) x := stepArchWeight_le _ _ _ _ _

lemma stepCutArchWeight_summable (N : ℕ) (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (stepCutArchWeight N s) :=
  ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2).of_nonneg_of_le
    (stepCutArchWeight_nonneg _ _) (stepCutArchWeight_le _ _)

lemma eventually_stepContains (N : ℕ) (s : ℤ) (p : List Triangle)
    (hp : ∀ v∈p,v.2.1 < N+1) :
    ∀ᶠ L : ℕ in atTop,∀ v∈p,steppedDomain N (s-(L:ℤ)) v := by
  have h : ∀ᶠ L : ℕ in atTop,∀ v∈p.toFinset,s-(L:ℤ) ≤ v.1 := by
    apply (p.toFinset.eventually_all).mpr
    intro v _
    filter_upwards [eventually_ge_atTop (s-v.1).toNat] with L hL
    omega
  filter_upwards [h] with L hL
  intro v hv
  have hband := hp v hv
  have hcol := hL v (List.mem_toFinset.mpr hv)
  unfold steppedDomain
  omega

lemma eventually_stepExcludes (N : ℕ) (s : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,∀ v∈p,steppedDomain N (s+(L:ℤ)) v ↔ v.2.1 < N := by
  have h : ∀ᶠ L : ℕ in atTop,∀ v∈p.toFinset,v.1<s+(L:ℤ) := by
    apply (p.toFinset.eventually_all).mpr
    intro v _
    filter_upwards [eventually_ge_atTop (v.1-s+1).toNat] with L hL
    omega
  filter_upwards [h] with L hL
  intro v hv
  have hcol := hL v (List.mem_toFinset.mpr hv)
  unfold steppedDomain
  omega

lemma stepArchWeight_eventually_tall (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,stepArchWeight N (s-(L:ℤ)) i j p=betweenArchWeight (N+1) i j p := by
  by_cases hp : ∀ v∈p,v.2.1 < N+1
  · filter_upwards [eventually_stepContains N s p hp] with L hL
    exact ite_eq_left hL
  · have hz : betweenArchWeight (N+1) i j p=0 := by
      apply ite_eq_right
      rintro ⟨_,ht⟩
      exact hp ht.2.2.2.2
    exact Eventually.of_forall (fun L => by simp only [stepArchWeight,hz,ite_self])

lemma stepArchWeight_eventually_short (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    ∀ᶠ L : ℕ in atTop,stepArchWeight N (s+(L:ℤ)) i j p=betweenArchWeight N i j p := by
  filter_upwards [eventually_stepExcludes N s p] with L hL
  have he : (∀ v∈p,steppedDomain N (s+(L:ℤ)) v) ↔ ∀ v∈p,v.2.1 < N := by
    exact forall_congr' (fun v => forall_congr' (hL v))
  simpa only [stepArchWeight,he] using betweenArchWeight_restrict N i j p

 

theorem step_cut_mass_tall_limit {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Tendsto (fun L : ℕ => ∑' x,stepCutArchWeight N (s-(L:ℤ)) x) atTop (𝓝 (moment (N+1))) := by
  rw [physical_moment_eq_cut_sum h]
  apply tendsto_tsum_of_dominated_convergence
    ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2)
  · intro x
    exact tendsto_const_nhds.congr' ((stepArchWeight_eventually_tall N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2).mono (fun L hL => hL.symm))
  · exact Eventually.of_forall (fun L x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (stepCutArchWeight_nonneg _ _ _)]
      exact stepCutArchWeight_le _ _ _)

 

theorem step_cut_mass_short_limit {N : ℕ} (s : ℤ)
    (h : StripSumsFinite (N+1)) (h₀ : StripSumsFinite N) :
    Tendsto (fun L : ℕ => ∑' x,stepCutArchWeight N (s+(L:ℤ)) x) atTop (𝓝 (moment N)) := by
  rw [physical_moment_eq_cut_sum h₀]
  apply tendsto_tsum_of_dominated_convergence
    ((cutArchWeight_summable_iff (N+1) h.1).mpr h.2.2.2.2)
  · intro x
    exact tendsto_const_nhds.congr' ((stepArchWeight_eventually_short N s (-(x.1.1:ℤ)) ((x.1.2:ℤ)+1) x.2).mono (fun L hL => hL.symm))
  · exact Eventually.of_forall (fun L x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (stepCutArchWeight_nonneg _ _ _)]
      exact stepCutArchWeight_le _ _ _)

end
end CriticalStrip

end OAI
