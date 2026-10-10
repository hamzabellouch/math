import OAI.NumberTheory.DirichletL.Descent.CanonicalRankMoments

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialCanonicalEnergy
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalQuadraticSieve
open InverseMoment InverseInitialClippedColumns SecondPassArithmetic CanonicalCoefficientClass
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem normalization_change (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(w:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F G:ℝ)(hZ:0<Z):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^(G-F)*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G := by
  have he:Z^F*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F=
      Z^G*normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z G:=
    (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ F).symm.trans
      (columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows w W X hZ G)
  apply mul_left_cancel₀ (Real.rpow_pos_of_pos hZ F).ne'
  rw [←mul_assoc,←Real.rpow_add hZ,show F+(G-F)=G by ring]
  exact he

omit [DecidableEq σ] in
theorem energy_range_weight_le (pool:Finset ι)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows largeRows:Finset O)(w v:Ideal O→ℝ)(W:ℝ→ℂ)
    (X Z F:ℝ)(hrows:rows⊆largeRows)(hw:∀f∈labels,0≤w f)(hv:∀f∈labels,w f≤v f):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows w W X Z F≤
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels largeRows v W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul (hv f hf)
    (Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _=>sq_nonneg _))
    (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
    ((hw f hf).trans (hv f hf))

omit [DecidableEq σ] in
theorem initial_child_from_rank (pool:Finset ι)(base Ψ:O→*ℂ)
    (slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:𝓢(ℝ,ℂ))
    (Z Mcap Fcap z c eps A N V M Q η:ℝ)(K degree:ℕ)(m:O)
    (hZ:1<Z)(hbase:IsBaseRayTwist base Ψ)(hm:m≠0)
    (hN:0≤N)(hV:0≤V+2*η)(hM:0≤M)(hQ:0≤Q)
    (hMcap:M≤Mcap)(hFcap:N+(V+2*η)≤Fcap)
    (hmargin:CanonicalMargins (N+(V+2*η)) M Q z c)
    (hmnorm:‖eisEmbedding m‖^2=Z^Q)(hsub:subslots⊆slots)
    (labels:Finset (Ideal O))(hlabels:∀f∈labels,Admissible f ∧ (f.absNorm:ℝ)≤Z^(V+2*η))
    (rows:Finset O)(hrows:rows⊆nonzeroChildFrequencyBall 1 (Z^M))
    (weight:Ideal O→ℝ)(hw:∀f∈labels,0≤weight f)
    (hweight:∀f∈labels,weight f≤secondLabelWeight K f)(s:ℝ)
    (hmoment:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mcap Fcap z c eps A K degree):
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels rows weight
      (childLogTest W s) (Z^N) Z (N+V)≤A*Z^(N+V+eps+4*η)*(1+‖s‖)^(2*degree) := by
  have hcanon:=hmoment Ψ hbase m hm N (V+2*η) M Q hN hV hM hQ hMcap hFcap hmargin hmnorm
    subslots hsub labels hlabels s
  rw [normalization_change p hp hcop hg pool Ψ m subslots lists a labels rows weight
    (childLogTest W s) (Z^N) Z (N+V) (N+(V+2*η)) (zero_lt_one.trans hZ)]
  apply (mul_le_mul_of_nonneg_left
    ((energy_range_weight_le p hp hcop hg pool Ψ m subslots lists a labels rows
      (nonzeroChildFrequencyBall 1 (Z^M)) weight (secondLabelWeight K) (childLogTest W s)
      (Z^N) Z (N+(V+2*η)) hrows hw hweight).trans hcanon)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [show N+(V+2*η)-(N+V)=2*η by ring]
  calc
    _=A*(Z^(2*η)*Z^(N+(V+2*η)+eps))*(1+‖s‖)^(2*degree):=by ring
    _=_:=by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      congr 3
      ring

end SevenEighths.InverseInitialCanonicalEnergy

end

end OAI
