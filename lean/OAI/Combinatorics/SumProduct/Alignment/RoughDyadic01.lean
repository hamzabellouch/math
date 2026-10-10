import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughReal01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
open scoped BigOperators
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughAnalyticRationalization
open _root_.Polynomial _root_.OAI.Polynomial Filter Finset RoughScales
open RoughRationalBlock RoughCharacterThinning RoughJointCoefficients
open FinitePieceAverages RoughSamplingWeights ComparableBoxLeibman
open CorrectedBoxLeibman PolynomialLineCoefficients TriangularLatticeRecovery

lemma cast_progression_bounds {a b N K : ℕ} (h : a+b*K≤N)
    (z : ℤ) (hz : 0≤z) (hzK : z≤K) :
    0≤(a:ℤ)+(b:ℤ)*z ∧ (a:ℤ)+(b:ℤ)*z≤N := by
  constructor
  · positivity
  · have hmul:=mul_le_mul_of_nonneg_left hzK (Int.natCast_nonneg b)
    have hn : (a:ℤ)+(b:ℤ)*(K:ℤ)≤N:=by exact_mod_cast h
    omega

lemma split_comp {v s w H : ℕ} {Z B : ℝ}
    {θ : PolynomialLineCoefficients.Grid v s→ℝ[X]}
    {a b : ℕ} {M : PolynomialLineCoefficients.Grid v s→ℚ[X]}
    (h : Split w H Z B θ a b M) :
    Split w H Z B (fun I=>(θ I).comp (C (a:ℝ)+C (b:ℝ)*X)) 0 1 M := by
  rcases h with ⟨hdeg,hden,hint,herr,hzero⟩
  refine ⟨hdeg,hden,hint,?_,?_⟩
  · simpa only [zero_add,one_mul,eval_comp,eval_add,eval_C,eval_mul,eval_X,
      Nat.cast_add,Nat.cast_mul] using herr
  · simpa only [zero_add,one_mul,eval_comp,eval_add,eval_C,eval_mul,eval_X,
      Nat.cast_add,Nat.cast_mul] using hzero

section Nilmanifold
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1) = ⊥)
variable (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g ∈ H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i = 0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
variable [MeasurableSpace (G⧸Γ)]
variable [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance roughDyadic01NilmanifoldTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem rational_split_from_discrepancies
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B₀ : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB₀ : 0<B₀) (hη : 0<η)
    {w : ℕ→ℕ} {S Z : ℕ→ℝ}
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ),∃ B : ℝ,1 ≤ B ∧
      ∀ h : ℕ,2*((v+1)*s+1)≤ h →∃ N : ℕ,∀ᶠ n in atTop,
      ∀ (a₀ m : ℤ),0 < m →Smooth (w n) m →
      (∀ z : ℤ,0≤z →z≤N →S n≤((a₀+m*z:ℤ):ℝ) ∧ ((a₀+m*z:ℤ):ℝ)<2*S n)→
      (∀ z : ℤ,0≤z →z≤N →Rough (w n) (a₀+m*z))→
      ∀ f : (Fin (v+1)→ℤ)→G,LeibmanSquare.Polynomial H 0 f →
      ∀ (lo hi : Fin (N+1)→Fin v→ℝ) (res : Fin (N+1)→Fin v→ℤ)
        (F : Fin (N+1)→C(G⧸Γ,ℂ)),
      (∀ j i,c₀*Z n≤hi j i-lo j i)→
      (∀ j i,-C₀*Z n≤lo j i ∧ hi j i≤C₀*Z n)→
      (∀ j,LipschitzWith B₀ (F j) ∧ ‖F j‖≤B₀)→
      (∀ j,η≤‖mean (boxIndices (lo j) (hi j) (fun _=>0) 1)
          (fun x=>F j (QuotientGroup.mk (f (Fin.cons (j.val:ℤ) x)))) -
        mean (physicalResidueBox (lo j) (hi j) (res j) (a₀+m*(j.val:ℤ)).natAbs)
          (fun x=>F j (QuotientGroup.mk (f (Fin.cons (j.val:ℤ) x))))‖) →
      ∃ a b : ℕ,0 < b ∧ a+b*h≤N ∧ Smooth (w n) (m*(b:ℤ)) ∧
        ∃ ξ∈U,ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ θ : PolynomialLineCoefficients.Grid v s→ℝ[X],
          (∀ I,(θ I).natDegree ≤ s) ∧
          (∀ z : ℤ,∀ x : Fin v→ℤ,
            gridEval (fun I=>(θ I).eval (z:ℝ)) (fun i=>(x i:ℝ)) =
              (ξ (f (Fin.cons ((a:ℤ)+(b:ℤ)*z) x))).toAdd) ∧
          ∃ M : PolynomialLineCoefficients.Grid v s→ℚ[X],Split (w n) h (Z n) B θ 0 1 M := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,T,hA,hT,hchar⟩:=common_character_from_discrepancies
    c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ B₀ η hc₀ hC₀ hB₀ hη
  obtain ⟨B,hB,hrat⟩:=eventual_split v s hA hw hS hZ
  refine ⟨U,B,hB,?_⟩
  intro h hh
  obtain ⟨K,hK,hKrat⟩:=hrat h hh
  obtain ⟨N,hNchar⟩:=hchar K
  refine ⟨N,?_⟩
  have hzscale : ∀ᶠ n in atTop,2*T≤Z n/S n:=by
    simpa only [pow_one] using (hZ 1).eventually (eventually_ge_atTop (2*T))
  filter_upwards [hKrat,hw.eventually (eventually_ge_atTop N),
    hS.eventually (eventually_ge_atTop 1),hzscale] with n hratn hwn hSn hZn
  intro a₀ m hm hms hscale hrough f hf lo hi res F hside hbox hF hbad
  let k : Fin (N+1)→ℕ:=fun j=>(a₀+m*(j.val:ℤ)).natAbs
  have hscalej (j : Fin (N+1)):=hscale (j.val:ℤ) (by positivity)
    (by exact_mod_cast Nat.le_of_lt_succ j.isLt)
  have hposj (j : Fin (N+1)) : 0<(a₀+m*(j.val:ℤ):ℤ):=by
    have h:=lt_of_lt_of_le (by linarith : (0:ℝ)<S n) (hscalej j).1
    exact_mod_cast h
  have hkj (j : Fin (N+1)) : ((k j:ℕ):ℝ)=((a₀+m*(j.val:ℤ):ℤ):ℝ):=by
    simp only [k,Nat.cast_natAbs,abs_of_nonneg (by exact_mod_cast (hposj j).le)]
  have hk (j : Fin (N+1)) : 0<k j:=Int.natAbs_pos.mpr (hposj j).ne'
  have hTk (j : Fin (N+1)) : T≤Z n/(k j):=by
    apply (le_div_iff₀ (by exact_mod_cast hk j)).mpr
    rw [hkj]
    have hZ' : (2*T)*S n≤Z n:=(le_div_iff₀ (by linarith)).mp hZn
    calc T*((a₀+m*(j.val:ℤ):ℤ):ℝ) ≤ T*(2*S n):=mul_le_mul_of_nonneg_left
          (hscalej j).2.le (by linarith)
         _ ≤ Z n:=by nlinarith
  obtain ⟨a,b,hb,hab,ξ,hξ,hξn,hξc,hξZ,θ,hθ,he,hobs⟩:=hNchar (Z n) k hk hTk f hf
    lo hi res F hside hbox hF hbad
  have hbN : b≤N:=by nlinarith
  have hbs : Smooth (w n) (b:ℤ):=smooth_of_abs_le (by exact_mod_cast hb.ne')
    (by simpa using hbN.trans hwn)
  have hmbs : Smooth (w n) (m*(b:ℤ)):=smooth_mul hms hbs
  choose p u hpu huu hcoeff using hobs
  let idx : ℤ→Fin (K+1):=fun z=>⟨min z.toNat K,by omega⟩
  have hidx (z : ℤ) (hz : 0≤z) (hzK : z≤K) : ((idx z).val:ℤ)=z:=by
    dsimp [idx]
    rw [Nat.min_eq_left (Int.toNat_le.mpr hzK),Int.toNat_of_nonneg hz]
  have hidxr (z : ℤ) (hz : 0≤z) (hzK : z≤K) : ((idx z).val:ℝ)=(z:ℝ):=by
    exact_mod_cast hidx z hz hzK
  have htime (z : ℤ) : a₀+m*((a:ℤ)+(b:ℤ)*z)=(a₀+m*(a:ℤ))+(m*(b:ℤ))*z:=by ring
  have hkidx (z : ℤ) (hz : 0≤z) (hzK : z≤K) :
      k (progressionIndex a b hab (idx z))=((a₀+m*(a:ℤ))+(m*(b:ℤ))*z).natAbs:=by
    simp only [k,progressionIndex_val,Nat.cast_add,Nat.cast_mul,hidx z hz hzK,htime]
  obtain ⟨c',d',hd',hdN,hcd,hsm,M,hM⟩:=hratn (a₀+m*(a:ℤ)) (m*(b:ℤ))
    (mul_pos hm (by exact_mod_cast hb)) hmbs
    (fun z hz hzK=>by
      simpa only [htime] using hscale _ (cast_progression_bounds hab z hz hzK).1
        (cast_progression_bounds hab z hz hzK).2)
    (fun z hz hzK=>by
      simpa only [htime] using hrough _ (cast_progression_bounds hab z hz hzK).1
        (cast_progression_bounds hab z hz hzK).2)
    θ hθ (fun z=>p (idx z)) (fun z=>u (idx z))
    (fun z hz hzK=>by
      rcases hpu (idx z) with hp | hp
      · rw [hp]; omega
      · rw [hp]; exact hk _)
    (fun z hz hzK=>by simpa only [hkidx z hz hzK] using hpu (idx z))
    (fun z _ _=>huu (idx z))
    (fun z hz hzK I hI=>by simpa only [hidxr z hz hzK] using hcoeff (idx z) I hI)
  let θ' : PolynomialLineCoefficients.Grid v s→ℝ[X]:=fun I=>(θ I).comp (C (c':ℝ)+C (d':ℝ)*X)
  refine ⟨a+b*c',b*d',Nat.mul_pos hb hd',?_,?_,ξ,hξ,hξn,hξc,hξZ,θ',
    fun I=>affine_degree (hθ I) _ _,?_,M,split_comp hM⟩
  · nlinarith
  · simpa only [Nat.cast_mul,mul_assoc] using hsm
  · intro z x
    have h:=he ((c':ℤ)+(d':ℤ)*z) x
    have ht : (a:ℤ)+(b:ℤ)*((c':ℤ)+(d':ℤ)*z)=((a+b*c':ℕ):ℤ)+((b*d':ℕ):ℤ)*z:=by
      push_cast
      ring
    simpa [θ',Int.cast_add,Int.cast_mul,ht] using h

end Nilmanifold
end RoughAnalyticRationalization

end
 
end

section
 

 

noncomputable section
open scoped BigOperators commutatorElement
namespace RoughDyadicFiltration
open RationalLattice MalcevCharacters CubeFaces LeibmanSquare RealPolynomialDegree
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

def weight (D : ℕ) (i : Fin n) : ℕ:=D*2^i.val
lemma weight_mono (D : ℕ) : Monotone (weight (n:=n) D):=by
  intro i j hij
  exact Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega) hij)

def cutoff (n D k : ℕ) : ℕ:=
  Classical.choose (MalcevWeightedCoordinates.exists_weight_cutoff (weight (n:=n) D) (weight_mono D) k)
lemma cutoff_le (D k : ℕ) : cutoff n D k≤n:=
  (Classical.choose_spec (MalcevWeightedCoordinates.exists_weight_cutoff (weight (n:=n) D) (weight_mono D) k)).1
lemma cutoff_spec (D k : ℕ) (i : Fin n) : weight D i<k ↔ i.val<cutoff n D k:=
  (Classical.choose_spec (MalcevWeightedCoordinates.exists_weight_cutoff (weight (n:=n) D) (weight_mono D) k)).2 i

def level (D k : ℕ) : Subgroup G:=coordinateTail c (cutoff n D k)
lemma mem_level (D k : ℕ) (g : G) : g∈level c D k ↔ ∀ i : Fin n,weight D i<k→c.coord g i=0:=by
  simp only [level,mem_coordinateTail,← cutoff_spec]
lemma unweight_level (D k : ℕ) (g : G) :
    g∈level c D k ↔ ∀ i : Fin n,i.val<cutoff n D k→c.coord g i=0:=Iff.rfl
lemma level_antitone (D : ℕ) : Antitone (level c D):=by
  intro i j hij g hg
  rw [mem_level] at hg ⊢
  exact fun a ha=>hg a (ha.trans_le hij)
lemma level_top {D k : ℕ} (hk : k≤D) : level c D k=⊤:=by
  ext g
  simp only [mem_level,Subgroup.mem_top,iff_true]
  intro i hi
  have h1 : 1≤2^i.val:=Nat.one_le_pow _ _ (by omega)
  have : D≤weight D i:=by dsimp [weight]; nlinarith
  omega
lemma level_terminal (D : ℕ) : level c D (D*2^n+1)=⊥:=by
  apply le_antisymm _ bot_le
  intro g hg
  rw [mem_level] at hg
  apply Subgroup.mem_bot.mpr
  apply c.coord.injective
  funext i
  rw [c.one_coord]
  apply hg
  have hp : 2^i.val≤2^n:=Nat.pow_le_pow_right (by omega) i.isLt.le
  dsimp [weight]
  nlinarith
lemma twice_weight {j i : Fin n} (hji : j.val < i.val) (D : ℕ) : 2*weight D j≤weight D i:=by
  have hp : 2^(j.val+1)≤2^i.val:=Nat.pow_le_pow_right (by omega) hji
  rw [pow_succ] at hp
  dsimp [weight]
  nlinarith [Nat.mul_le_mul_left D hp]

lemma commutator_le_of_le (D : ℕ) {k l : ℕ} (hkl : k≤l) :
    ⁅level c D k,level c D l⁆≤level c D (k+l):=by
  apply Subgroup.commutator_le.mpr
  intro g hg x hx
  rw [mem_level] at hx ⊢
  intro i hi
  have hxlow : x∈coordinateTail c i.val:=by
    intro j hj
    apply hx
    have h:=twice_weight hj D
    omega
  exact coordinateTail_commutator c i.val g x hxlow i (by omega)
lemma bracket (D k l : ℕ) : ⁅level c D k,level c D l⁆≤level c D (k+l):=by
  rcases le_total k l with h | h
  · exact commutator_le_of_le c D h
  · rw [Subgroup.commutator_comm,Nat.add_comm]
    exact commutator_le_of_le c D h

def filtration (D : ℕ) : Filtration G where
  level:=level c D
  antitone:=level_antitone c D
  commutator_le:=bracket c D
instance normal (D k : ℕ) : ((filtration c D).level k).Normal:=
  coordinateTail_normal c _
lemma filtration_zero (D : ℕ) : (filtration c D).level 0=⊤:=level_top c (Nat.zero_le D)
lemma filtration_one {D : ℕ} (hD : 0<D) : (filtration c D).level 1=⊤:=level_top c hD

variable [IsTopologicalGroup G] (hsk : SecondKind c)
include hsk in
omit [IsTopologicalGroup G] in
lemma coordinate_adapted {v D : ℕ} (P : (Fin v→ℝ)→G)
    (hP : ∀ i,HasDegree (fun x=>c.coord (P x) i) D) :
    LeibmanSquare.Polynomial (filtration c D) 0 P:=by
  classical
  have haxis (i : Fin n) : LeibmanSquare.Polynomial (filtration c D) 0
      (fun x=>axis c i (c.coord (P x) i)):=by
    obtain ⟨p,hp,he⟩:=hP i
    have hdiff : ScalarDifferenceDegree.DegreeAtMost D (fun x=>c.coord (P x) i):=by
      simp_rw [he]
      exact ScalarDifferenceDegree.eval_polynomial p hp
    exact ScalarDifferenceDegree.polynomial_power (filtration c D)
      (MalcevTailSection.axisHom c hsk i) D (by
        intro r
        change _∈level c D D
        rw [level_top c le_rfl]
        trivial) hdiff
  have hp:=CubeTaylorExpansion.polynomial_list_prod (filtration c D)
    (List.finRange n) (fun i x=>axis c i (c.coord (P x) i)) (fun i _=>haxis i)
  convert hp using 1
  funext x
  simp only [← List.ofFn_eq_map]
  exact hsk.ordered (P x)

include hsk in
 

omit [IsTopologicalGroup G] in
theorem logarithmic_adapted : ∃ C : ℕ,0<C ∧ ∀ v d : ℕ,
    let D:=max 1 (C*d)
    (filtration c D).level 0=⊤ ∧ (filtration c D).level 1=⊤ ∧
    (filtration c D).level (D*2^n+1)=⊥ ∧
    (∀ k,cutoff n D k≤n) ∧
    (∀ k g,g∈(filtration c D).level k ↔ ∀ i : Fin n,i.val<cutoff n D k→c.coord g i=0) ∧
    ∀ P : (Fin v→ℝ)→G,(∀ i,HasDegree (fun x=>canonicalLog c (P x) i) d)→
      LeibmanSquare.Polynomial (filtration c D) 0 P ∧
      LeibmanSquare.Polynomial (filtration c D) 0 (fun x : Fin v→ℤ=>P (fun i=>(x i:ℝ))) := by
  obtain ⟨C,hC,hcoord⟩:=coord_degree_bound c
  refine ⟨C,hC,fun v d=>⟨filtration_zero c _,filtration_one c (by omega),
    level_terminal c _,fun k=>cutoff_le _ _,fun k g=>unweight_level c _ _ g,?_⟩⟩
  intro P hP
  have hp:=coordinate_adapted c hsk P
    (fun i=>RealPolynomialDegree.mono (hcoord v d P hP i) (le_max_right 1 (C*d)))
  exact ⟨hp,RoughLogPolynomialAdaptation.restrict_integer _ P hp⟩

end RoughDyadicFiltration

end
end
end

end OAI
