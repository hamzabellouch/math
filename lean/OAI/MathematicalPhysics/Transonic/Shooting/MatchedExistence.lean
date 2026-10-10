import OAI.MathematicalPhysics.Transonic.Shooting.ShootingMatch
import OAI.MathematicalPhysics.Transonic.Shooting.SonicShootingFamily

namespace OAI

namespace SepticProfile.SonicShooting

theorem exists_matched_pair : Nonempty MatchedPair := by
  obtain ⟨F⟩ := exists_family
  obtain ⟨A⟩ := AxisShooting.exists_family
  obtain ⟨p,hp⟩ := exists_match F A
  exact ⟨⟨F,A,p,hp⟩⟩

end SepticProfile.SonicShooting

end OAI
