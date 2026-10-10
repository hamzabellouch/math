import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox02
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open TriangularLatticeRecovery
variable {v : ℕ} {E α : Type*} [Fintype E] [DecidableEq E]

 

theorem direction_character_recovery (m : E→(Fin v→₀ℕ)) (hm : Function.Injective m)
    (D : ℕ) (hD : ∀ e, (m e).sum (fun _ k => k)≤D)
    (U : Finset α) (B : ℕ) (hB : 0<B) :
    ∃ L K : ℕ, 0<L ∧ 0<K ∧
    ∀ X A : ℝ, 0≤X → 0≤A → ∀ a : α→E→ℝ,
      (∀ q : Fin v→Fin L, ∃ ξ∈U, ∃ r : ℕ, 0<r ∧ r≤B ∧
        ∀ j : ℕ, 0<j → circleNorm ((r:ℝ)*
          ∑ e, (if (m e).sum (fun _ k => k)=j then a ξ e else 0)*
            (gridMonomial m q e:ℝ))*X^j≤A) →
      ∃ ξ∈U, ∃ r : ℕ, 0<r ∧ r≤K ∧ ∀ e,
        0<(m e).sum (fun _ k => k) →
        circleNorm ((r:ℝ)*a ξ e)*X^((m e).sum (fun _ k => k))≤(K:ℝ)*A := by
  classical
  let T := U ×ˢ Finset.range (B+1)
  let Z := T.card+1
  let L := D*Z+1
  have hL : 0<L := by dsimp [L]; omega
  have hZ : 0<Z := by dsimp [Z]; omega
  have hDL : D*Z<L := by dsimp [L]; omega
  obtain ⟨K,hK,hweights⟩ := uniform_dense_grid_weights m hm D hD L
  refine ⟨L,B*K,hL,Nat.mul_pos hB hK,?_⟩
  intro X A hX hA a hget
  let P (q : Fin v→Fin L) (p : α×ℕ) := 0<p.2 ∧
    ∀ j : ℕ, 0<j → circleNorm ((p.2:ℝ)*
      ∑ e, (if (m e).sum (fun _ k => k)=j then a p.1 e else 0)*
        (gridMonomial m q e:ℝ))*X^j≤A
  have hget' (q : Fin v→Fin L) (_ : q∈Finset.univ) : ∃ p∈T, P q p := by
    obtain ⟨ξ,hξ,r,hr,hrB,hb⟩ := hget q
    exact ⟨(ξ,r),Finset.mem_product.mpr ⟨hξ,Finset.mem_range.mpr (Nat.lt_succ_of_le hrB)⟩,hr,hb⟩
  obtain ⟨Q,hQU,hQne,hQc,p,hp,hP⟩ := SquareInduction.finite_dense_choice_general T
    (Finset.univ : Finset (Fin v→Fin L)) 1 ((L:ℝ)^v) (by norm_num) (pow_pos (Nat.cast_pos.mpr hL) _)
    (by simp) P hget'
  have hcountNat : L^v≤Q.card*Z := by
    have hZr : 0<(Z:ℝ) := Nat.cast_pos.mpr hZ
    have hQc' : (L:ℝ)^v/(Z:ℝ)≤(Q.card:ℝ) := by
      simpa only [Z,Nat.cast_add,Nat.cast_one,one_div,one_mul,mul_comm,div_eq_mul_inv] using hQc
    have hh := (div_le_iff₀ hZr).mp hQc'
    exact_mod_cast hh
  have hLn : (0:ℚ≥0)<L := Nat.cast_pos.mpr hL
  have hZn : (0:ℚ≥0)<Z := Nat.cast_pos.mpr hZ
  have hden : (D:ℚ≥0)/(L:ℚ≥0)<(Q.card:ℚ≥0)/(L:ℚ≥0)^v := by
    calc
      _ < 1/(Z:ℚ≥0) := by
        apply (div_lt_div_iff₀ hLn hZn).mpr
        simpa only [one_mul,Nat.cast_mul] using (show (D:ℚ≥0)*(Z:ℚ≥0)<L by exact_mod_cast hDL)
      _ ≤ _ := by
        apply (div_le_div_iff₀ hZn (pow_pos hLn _)).mpr
        simpa only [one_mul] using (show (L:ℚ≥0)^v≤(Q.card:ℚ≥0)*(Z:ℚ≥0) by exact_mod_cast hcountNat)
  obtain ⟨b,hb,hbK,w,hw,hwK⟩ := hweights Q hden
  have hpU : p.1∈U := (Finset.mem_product.mp hp).1
  have hprB : p.2≤B := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
  have hpr : 0<p.2 := (hP _ hQne.choose_spec).1
  refine ⟨p.1,hpU,b*p.2,Nat.mul_pos hb hpr,?_,?_⟩
  · exact (Nat.mul_le_mul hbK hprB).trans_eq (Nat.mul_comm K B)
  · intro e he
    have hline (q : Q) (j : ℕ) (hj : 0<j) :
        circleNorm (∑ f, (if (m f).sum (fun _ k => k)=j then (p.2:ℝ)*a p.1 f else 0)*
          (gridMonomial m q.val f:ℝ))*X^j≤A := by
      have hh := (hP q.val q.property).2 j hj
      have heq : (∑ f, (if (m f).sum (fun _ k => k)=j then (p.2:ℝ)*a p.1 f else 0)*
          (gridMonomial m q.val f:ℝ))=(p.2:ℝ)*
          ∑ f, (if (m f).sum (fun _ k => k)=j then a p.1 f else 0)*(gridMonomial m q.val f:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        split_ifs <;> ring
      rwa [heq]
    have hh := homogeneous_recovery (fun e => (m e).sum (fun _ k => k))
      (fun q : Q => gridMonomial m q.val) b w hw (fun e => (p.2:ℝ)*a p.1 e) X A hX hline e he
    have hBK : (K:ℝ)≤(B*K:ℕ) := by exact_mod_cast Nat.le_mul_of_pos_left K hB
    have hfin := hh.trans ((mul_le_mul_of_nonneg_right (hwK e) hA).trans
      (mul_le_mul_of_nonneg_right hBK hA))
    simpa only [Nat.cast_mul,mul_assoc] using hfin

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman

def gridExponent {v s : ℕ} (e : Grid v s) : Fin v→₀ℕ := Finsupp.equivFunOnFinite.symm (fun i => (e i).val)

@[simp] lemma gridExponent_apply {v s : ℕ} (e : Grid v s) (i : Fin v) : gridExponent e i=(e i).val := rfl
lemma gridExponent_injective (v s : ℕ) : Function.Injective (gridExponent (v:=v) (s:=s)) := by
  intro e f h
  funext i
  apply Fin.ext
  exact congrArg (fun g : Fin v→₀ℕ => g i) h
lemma gridExponent_degree {v s : ℕ} (e : Grid v s) :
    (gridExponent e).sum (fun _ k => k)=PolynomialLineCoefficients.totalDegree e := by
  rw [Finsupp.sum_fintype]
  · rfl
  · simp
lemma gridMonomial_eq_prod {v s L : ℕ} (q : Fin v→Fin L) (e : Grid v s) :
    (gridMonomial gridExponent q e:ℝ)=∏ i, ((q i).val:ℝ)^(e i).val := by
  simp only [gridMonomial,Int.cast_prod,Int.cast_pow,Int.cast_natCast,gridExponent_apply]
end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open TriangularLatticeRecovery PolynomialLineCoefficients

lemma rescale_line_bound {N H T s j : ℕ} (hT : 0<T) (hNH : N≤2*T*H) (hjs : j ≤ s)
    (b A : ℝ) (hA : 0≤A) (hb : circleNorm b*(H:ℝ)^j≤A) :
    circleNorm b*(N:ℝ)^j≤(2*(T:ℝ))^s*A := by
  have hT1 : 1≤2*(T:ℝ) := by exact_mod_cast (show 1≤2*T by omega)
  have hpow : (N:ℝ)^j≤(2*(T:ℝ))^s*(H:ℝ)^j := by
    calc
      _ ≤ (2*(T:ℝ)*(H:ℝ))^j := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hNH) _
      _ = (2*(T:ℝ))^j*(H:ℝ)^j := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT1 hjs) (by positivity)
  calc
    _ ≤ circleNorm b*((2*(T:ℝ))^s*(H:ℝ)^j) := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = (2*(T:ℝ))^s*(circleNorm b*(H:ℝ)^j) := by ring
    _ ≤ _ := by
      simpa only [mul_comm] using
        mul_le_mul hb (le_refl ((2*(T:ℝ))^s)) (by positivity) hA

 

theorem corrected_box_recovery {α : Type*} (v s : ℕ) (U : Finset α)
    (δ A : ℝ) (hδ : 0<δ) (hA : 0<A) :
    ∃ K N₁ : ℕ, 0<K ∧ 0<N₁ ∧ ∃ E : ℝ, 0<E ∧
      ∀ N : ℕ, N₁≤N → ∀ f : α→(Fin v→ℤ)→ℝ,
      (∀ ξ, LinePolynomial v s (f ξ)) →
      ∀ a : α→Grid v s→ℝ,
      (∀ ξ x, gridEval (a ξ) (fun i => (x i:ℝ))=f ξ x) →
      (∀ M : ℕ, 0<M → ∀ q : Fin v→ℕ, 2*(M:ℝ)*(∑ i,q i:ℕ)/N≤δ/8 →
        ∃ ξ∈U, ∃ S : Set (Fin v→ℕ),
          (δ/8)/((U.card:ℝ)+1)*(N:ℝ)^v≤(BoxCounting.count v N S:ℝ) ∧
          ∀ x∈S, ∀ j : ℕ, 0<j → circleNorm
            (lineCoefficient (s:=s) (f ξ) (fun i => (q i:ℤ)) j (fun i => (x i:ℤ)))≤A/(M:ℝ)^j) →
      ∃ ξ∈U, ∃ r : ℕ, 0<r ∧ r≤K ∧ ∀ e : Grid v s, 0<totalDegree e →
        circleNorm ((r:ℝ)*a ξ e)*(N:ℝ)^(totalDegree e)≤E := by
  classical
  have hρ : 0<(δ/8)/((U.card:ℝ)+1) := by positivity
  obtain ⟨C,N₀,hC,hN₀,ε,hε,horigin⟩ := dense_origin_multiplier v s _ hρ
  have hdeg (e : Grid v s) : (gridExponent e).sum (fun _ k => k)≤v*s := by
    rw [gridExponent_degree]
    calc
      _ ≤ ∑ _ : Fin v, s := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (e i).isLt)
      _ = _ := by simp
  obtain ⟨L,K,hL,hK,hrecover⟩ := direction_character_recovery gridExponent (gridExponent_injective v s)
    (v*s) hdeg U (C^(s+1)) (pow_pos hC _)
  obtain ⟨T,N₁,hT,hN₁,hN₀₁,hscale⟩ := choose_short_scale v L N₀ δ ε A hδ hε hA.le
  let E := (K:ℝ)*((2*(T:ℝ))^s*((C:ℝ)^(s+2)*A))
  refine ⟨K,N₁,hK,hN₁,E,by dsimp [E]; positivity,?_⟩
  intro N hN f hf a ha hsource
  obtain ⟨hH,hsmall,hNH,hshort⟩ := hscale N hN
  let M := N/T
  have hget (q : Fin v→Fin L) : ∃ ξ∈U, ∃ r : ℕ, 0<r ∧ r≤C^(s+1) ∧
      ∀ j : ℕ, 0<j → circleNorm ((r:ℝ)*
        ∑ e, (if (gridExponent e).sum (fun _ k => k)=j then a ξ e else 0)*
          (gridMonomial gridExponent q e:ℝ))*(N:ℝ)^j≤(2*(T:ℝ))^s*((C:ℝ)^(s+2)*A) := by
    obtain ⟨ξ,hξ,S,hSc,hS⟩ := hsource M hH (fun i => (q i).val) (hshort q)
    obtain ⟨r,hr,hrC,hrb⟩ := horigin N (hN₀₁.trans hN) M hH A hA.le hsmall (f ξ) (hf ξ)
      (fun i => ((q i).val:ℤ)) S hS hSc
    refine ⟨ξ,hξ,r,hr,hrC,?_⟩
    intro j hj
    have heq := lineCoefficient_origin (hf ξ) (a ξ) (ha ξ) (fun i => (q i).val) j
    simp only [gridExponent_degree,gridMonomial_eq_prod]
    rw [← heq]
    by_cases hjs : j ≤ s
    · exact rescale_line_bound hT hNH hjs _ _ (by positivity) (hrb j hj)
    · rw [lineCoefficient_above (hf ξ) 0 _ (Nat.lt_of_not_ge hjs),mul_zero,circleNorm_zero,zero_mul]
      positivity
  obtain ⟨ξ,hξ,r,hr,hrK,hb⟩ := hrecover (N:ℝ) ((2*(T:ℝ))^s*((C:ℝ)^(s+2)*A))
    (Nat.cast_nonneg _) (by positivity) a hget
  refine ⟨ξ,hξ,r,hr,hrK,?_⟩
  intro e he
  simpa only [gridExponent_degree] using hb e (by simpa only [gridExponent_degree] using he)

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction TriangularLatticeRecovery BoxPolynomialLines PolynomialLineCoefficients
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance correctedBox04QuotientTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma character_pow_toAdd [TopologicalSpace G] [IsTopologicalGroup G]
    (ξ : G→*Multiplicative ℝ) (r : ℕ) (g : G) :
    ((ξ^r) g).toAdd=(r:ℝ)*(ξ g).toAdd := by
  simp only [MonoidHom.pow_apply,toAdd_pow,nsmul_eq_mul]

lemma character_pow_ne (ξ : G→*Multiplicative ℝ) (hξ : ξ≠1) (r : ℕ) (hr : 0<r) : ξ^r≠1 := by
  intro he
  apply hξ
  ext g
  apply Multiplicative.toAdd.injective
  have hh := congrArg (fun χ : G→*Multiplicative ℝ => (χ g).toAdd) he
  rw [character_pow_toAdd] at hh
  change (r:ℝ)*(ξ g).toAdd=0 at hh
  change (ξ g).toAdd=0
  exact (mul_eq_zero.mp hh).resolve_left (Nat.cast_ne_zero.mpr (ne_of_gt hr))

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem box_monomial_large
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀≤N → ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ≤‖boxMean v N (fun x => F (QuotientGroup.mk (f (fun i => (x i:ℤ)))))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ a : Grid v s→ℝ, (∀ x, gridEval a (fun i => (x i:ℝ))=(ξ (f x)).toAdd) ∧
          ∀ e, 0<totalDegree e → circleNorm (a e)*(N:ℝ)^(totalDegree e)≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,hA,hU,hline⟩ := box_line_data c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v δ hδ
  obtain ⟨K,N₀,hK,hN₀,E,hE,hrec⟩ := corrected_box_recovery v s U δ A hδ hA
  let V := (U ×ˢ Finset.range (K+1)).image (fun p => p.1^p.2)
  refine ⟨V,E,hE,N₀,hN₀,?_⟩
  intro N hN f hf ⟨F,hFL,hFn,hd⟩
  have hscalar (ξ : G→*Multiplicative ℝ) : LinePolynomial v s (fun x => (ξ (f x)).toAdd) := by
    intro x z
    exact character_polynomial H s hs (polynomial_integer_line H hf x z) ξ
  have hex (ξ : G→*Multiplicative ℝ) := character_grid_expansion H s hs hf ξ
  choose a ha using hex
  obtain ⟨ξ,hξ,r,hr,hrK,hb⟩ := hrec N hN (fun ξ x => (ξ (f x)).toAdd) hscalar a ha
    (fun M hM z hz => hline N M (hN₀.trans_le hN) hM f hf F hFL hFn hd z hz)
  obtain ⟨hξne,hξc,hξΓ⟩ := hU ξ hξ
  refine ⟨ξ^r,Finset.mem_image.mpr ⟨(ξ,r),Finset.mem_product.mpr
    ⟨hξ,Finset.mem_range.mpr (Nat.lt_succ_of_le hrK)⟩,rfl⟩,character_pow_ne ξ hξne r hr,hξc.pow r,?_,
    fun e => (r:ℝ)*a ξ e,?_,hb⟩
  · intro g hg
    obtain ⟨z,hz⟩ := hξΓ g hg
    refine ⟨(r:ℤ)*z,?_⟩
    rw [character_pow_toAdd,hz]
    simp
  · intro x
    rw [character_pow_toAdd,← ha ξ x]
    simp only [gridEval,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

end CorrectedBoxLeibman

end
end
end
end
end

end OAI
