import Mathlib

namespace OAI

noncomputable section

namespace KKAsymptoticTransport

noncomputable section

open Filter

open scoped Topology

variable {I A:Type*} [NormedRing A] [NormedAlgebra ℂ A]

def NetBound (f:I → A) : Prop := ∃C:ℝ,0≤C ∧ ∀j,‖f j‖≤C

def netPair (w:List ((I → A)×A)) (j:I) : A :=
  (w.map fun z => z.1 j*z.2).prod

def centerNet (E:A →L[ℂ] A) (f:I → A) (j:I) : A := f j-E (f j)

def centeredWord (E:A →L[ℂ] A) (w:List ((I → A)×A)) :=
  w.map fun z => (centerNet E z.1,z.2)

def RelativeBlockLimits (L:Filter I) (E:A →L[ℂ] A) (S:Set (I → A)) : Prop :=
  ∀w:List ((I → A)×A),(∀z∈w,z.1∈S ∧ E z.2=0) →
    (w≠[] → Tendsto (fun j => E (netPair (centeredWord E w) j)) L (𝓝 0)) ∧
    (∀c∈S,Tendsto (fun j => E (netPair (centeredWord E w) j*centerNet E c j)) L (𝓝 0))

def AsymptoticBlockTransport : Prop :=
  ∀(L:Filter I) (E:A →L[ℂ] A) (S:Set (I → A)) (T:Set A),
    (∀a,E (E a)=E a) →
    (∀a b,E (a*E b)=E a*E b) →
    (∀c∈S,NetBound c) →
    (∀c∈S,Tendsto (fun j => E (c j)) L (𝓝 0)) →
    (∀c∈S,∀d∈S,∀x∈T,(fun j => c j*E x*d j)∈S) →
    RelativeBlockLimits L E S →
    ∀w:List ((I → A)×A),w≠[] → (∀z∈w,z.1∈S ∧ z.2∈T) →
      Tendsto (fun j => E (netPair w j)) L (𝓝 0)

end

end KKAsymptoticTransport
end

end OAI
