import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeHistorySize
import OAI.Combinatorics.MatchingCount.Graphs.OnlineGraphInvariant
import OAI.Combinatorics.MatchingCount.Complexity.OnlineStageCost

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped TreeFraction PhysicalStream ExecutableSource ExecutableScaling
open BitArithmetic Polynomial OnlineStage OnlineSchedule OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma product_bits (p : Trial.Parameters G) (j : ℕ) (hj : j ≤ p.K)
    (x : (FiniteTrial.layers p j hj).Ω) :
    FractionBound ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j)
      (product p (FiniteTrial.layers p j hj) x : ℝ) := by
  have h := FractionBound.prod Finset.univ (fun i=>((FiniteTrial.layers p j hj).ratios x i : ℝ)) (p.empiricalBound^2)
    (fun i _=>FiniteTrial.layers_ratio_bits p j hj x i)
  simpa only [product,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod,Finset.card_univ,Fintype.card_fin] using
    (FractionBound.nat (Z (completeGraph G.n))).mul h

noncomputable def sizeNorm (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData) : ℕ :=
  G.n+p.K+p.N+p.D+p.S+p.T+p.q+weight g+(Z (completeGraph G.n)+1).size
omit [Nontrivial (Fin G.n)] in
lemma sizeNorm_fields (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData) :
    G.n ≤ sizeNorm p g ∧ p.K ≤ sizeNorm p g ∧ p.N ≤ sizeNorm p g ∧ p.D ≤ sizeNorm p g ∧
    p.S ≤ sizeNorm p g ∧ p.T ≤ sizeNorm p g ∧ p.q ≤ sizeNorm p g ∧ weight g ≤ sizeNorm p g ∧
    (Z (completeGraph G.n)+1).size ≤ sizeNorm p g := by
  unfold sizeNorm;omega

noncomputable def vectorPolynomial : Polynomial ℕ :=
  let B : Polynomial ℕ := X+1
  B*(4*B+8*(B+B*B*(19+B+2*(B+B*B+1))+1)+6)+1
noncomputable def productPolynomial : Polynomial ℕ :=
  let B : Polynomial ℕ := X+1
  8*(B+B*(2*(B+B*B+1)+1)+1)+3
lemma vector_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale) ≤ vectorPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hn' := (Nat.size_le.mpr Nat.lt_two_pow_self : G.n.size ≤ G.n)
  have hn1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have hd1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (p.D+1).size ≤ p.D+1)
  have hs' := (Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hv:=history_vector_weight p j hj x
  have hj' : j ≤ sizeNorm p g+1 := by omega
  simp only [vectorPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ (sizeNorm p g+1)*(4*(sizeNorm p g+1)+8*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)*
    (19+(sizeNorm p g+1)+2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1))+1)+6)+1
  apply hv.trans
  have hNN : Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K) ≤ sizeNorm p g+1 := by
    change p.N ≤ _;omega
  gcongr <;> omega
lemma product_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ productPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have he := size_empiricalBound p
  have hS:=(Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hnn:=(Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have he' : p.empiricalBound.size ≤ (sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1 := by
    apply he.trans
    change p.S.size+p.N*(G.n+1).size+1 ≤ _
    gcongr <;> omega
  have hp2:=size_pow_le p.empiricalBound 2
  have hpj:=size_pow_le (p.empiricalBound^2) j
  have hmul:=size_mul_le (Z (completeGraph G.n)+1) ((p.empiricalBound^2)^j)
  have hb : ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j).size ≤
      (sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1 := by
    calc
      _ ≤ (Z (completeGraph G.n)+1).size+j*(2*p.empiricalBound.size+1)+1 := by
        have h:=Nat.mul_le_mul_left j hp2;omega
      _ ≤ _ := by gcongr <;> omega
  have hw:=fraction_weight_of_bound (product_bits p j hj x)
  simp only [productPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 8*((sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1)+3
  omega

noncomputable def statePolynomial : Polynomial ℕ := 100*(X+1)+2*vectorPolynomial+2*productPolynomial
lemma data_weight (g : ExecutableAdaptive.GraphData) (j K D T Q : ℕ) (v : Vector) :
    weight ((((g,List.replicate j false),(((List.replicate (2*K+2) false,List.replicate (2*K) false),D),
      (List.replicate T false,List.replicate Q false))),v))=
      weight g+2*j+8*K+weight D+2*T+2*Q+weight v+16 := by
  simp only [weight_prod,weight_replicate,show weight false=1 from rfl]
  omega
lemma stateSize_mk (d : SparseStageData) (S : ℕ) (q : Fraction) :
    stateSize ((d,S),q)=d.1.2.1.2+S+3+2*weight d+2*weight S+weight q := by
  unfold stateSize requestSize
  simp only [weight_prod]
  omega
lemma state_weight_bound (f : OnlineGraph.Edges→OnlineGraph.Edges) (p : Trial.Parameters G)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    stateSize (OnlineGraph.state f (represent p (FiniteTrial.layers p j hj) x)) ≤
      statePolynomial.eval (sizeNorm p (OnlineGraph.graph f (ExecutableAdaptive.graphRep G))) := by
  let g:=OnlineGraph.graph f (ExecutableAdaptive.graphRep G)
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hv:=vector_weight_bound p g j hj x
  have hp:=product_weight_bound p g j hj x
  have hD : FiniteTrial.sourceD (G:=G) p.K=p.D := FiniteTrial.sourceD_eq p.K
  have hT : tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.T := by
    rw [hD];exact Transport.endpoint_eq p.N p.D p.K _
  have hQ : copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.q := by rw [hD];rfl
  have hwd:=weight_nat_numeric p.D
  have hws:=weight_nat_numeric p.S
  change stateSize ((OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)),p.S),
    TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ _
  rw [stateSize_mk]
  have hw : weight (OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)))=
      weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
      weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16 := by
    change weight ((((g,List.replicate j false),(((List.replicate (2*p.K+2) false,List.replicate (2*p.K) false),
      FiniteTrial.sourceD (G:=G) p.K),(List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false,
        List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false))),
      vectorRep ((FiniteTrial.layers p j hj).state x).scale))=_
    rw [data_weight,hT,hQ,hD]
  rw [hw]
  change FiniteTrial.sourceD (G:=G) p.K+p.S+3+2*(weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16)+2*weight p.S+
      weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ statePolynomial.eval (sizeNorm p g)
  rw [hD]
  simp only [statePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega
end MatchingFPRAS.OnlineTrial

end OAI
